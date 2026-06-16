// Global state and UI element configuration for E-Paper Display (EPD) Controller
let sourceImage = null;
let originalImage = null;
let canvas, ctx;
let floatCanvas, floatCtx;
let originalCanvasData = null;
let startTime;

let currentParams = {
    'saturation': 100,
    'brightness': 100,
    'contrast': 100,
    'diffusion': 50,
    'ditherAlg': 'floydSteinberg'
};

let currentMode = 'color';
let canvasRotation = 0;
let isDrawing = false;
let lastX = 0;
let lastY = 0;
let currentTool = 'pen';
let brushSize = 3;
let brushColor = '#000000';
let imageScale = 100;
let imageOffset = { 'x': 0, 'y': 0 };
let isDraggingImage = false;
let dragStartPos = { 'x': 0, 'y': 0 };
let shiftKeyPressed = false;
let imageRotation = 0;
let isDrawingModeActive = false;
let isDragging = false;
let dragOffset = { 'x': 0, 'y': 0 };
let isResizing = false;

// Hardware BLE (Bluetooth Low Energy) variables
let bleDevice, gattServer, epdService, epdCharacteristic;
let msgIndex, appVersion, textDecoder;

// E-Screen resolution presets
const canvasSizes = [
    { 'name': '2.13_122_250', 'width': 122, 'height': 250 },
    { 'name': '4.2_400_300',   'width': 400, 'height': 300 },
    { 'name': '7.5_800_480',   'width': 800, 'height': 480 }
];

// Hardware color palettes
const threeColorPalette = [
    { 'name': 'Black', 'r': 0,   'g': 0,   'b': 0,   'value': 0 },
    { 'name': 'White', 'r': 255, 'g': 255, 'b': 255, 'value': 1 },
    { 'name': 'Red',   'r': 255, 'g': 0,   'b': 0,   'value': 2 }
];

const blackWhitePalette = [
    { 'name': 'Black', 'r': 0,   'g': 0,   'b': 0,   'value': 0 },
    { 'name': 'White', 'r': 255, 'g': 255, 'b': 255, 'value': 1 }
];

// --- Image Processing Functions ---

function adjustContrast(imageData, contrastValue) {
    const pixels = imageData.data;
    for (let i = 0; i < pixels.length; i += 4) {
        pixels[i]     = Math.min(255, Math.max(0, (pixels[i]     - 128) * contrastValue + 128)); // R
        pixels[i + 1] = Math.min(255, Math.max(0, (pixels[i + 1] - 128) * contrastValue + 128)); // G
        pixels[i + 2] = Math.min(255, Math.max(0, (pixels[i + 2] - 128) * contrastValue + 128)); // B
    }
    return imageData;
}

function adjustBrightness(imageData, brightnessValue) {
    const factor = brightnessValue / 100;
    const pixels = imageData.data;
    for (let i = 0; i < pixels.length; i += 4) {
        pixels[i]     = Math.min(255, Math.max(0, pixels[i]     * factor)); // R
        pixels[i + 1] = Math.min(255, Math.max(0, pixels[i + 1] * factor)); // G
        pixels[i + 2] = Math.min(255, Math.max(0, pixels[i + 2] * factor)); // B
    }
    return imageData;
}

function adjustSaturation(imageData, saturationValue) {
    const pixels = imageData.data;
    for (let i = 0; i < pixels.length; i += 4) {
        // Standard relative luminance formula for grayscale conversion
        const luminance = 0.299 * pixels[i] + 0.587 * pixels[i + 1] + 0.114 * pixels[i + 2];
        
        pixels[i]     = Math.min(255, Math.max(0, luminance + (pixels[i]     - luminance) * saturationValue));
        pixels[i + 1] = Math.min(255, Math.max(0, luminance + (pixels[i + 1] - luminance) * saturationValue));
        pixels[i + 2] = Math.min(255, Math.max(0, luminance + (pixels[i + 2] - luminance) * saturationValue));
    }
    return imageData;
}

function rgbToLab(r, g, b) {
    r = r / 255;
    g = g / 255;
    b = b / 255;

    r = r > 0.04045 ? Math.pow((r + 0.055) / 1.055, 2.4) : r / 12.92;
    g = g > 0.04045 ? Math.pow((g + 0.055) / 1.055, 2.4) : g / 12.92;
    b = b > 0.04045 ? Math.pow((b + 0.055) / 1.055, 2.4) : b / 12.92;

    r *= 100;
    g *= 100;
    b *= 100;

    let x = r * 0.4124 + g * 0.3576 + b * 0.1805;
    let y = r * 0.2126 + g * 0.7152 + b * 0.0722;
    let z = r * 0.0193 + g * 0.1192 + b * 0.9505;

    x /= 95.047;
    y /= 100.000;
    z /= 108.883;

    x = x > 0.008856 ? Math.pow(x, 1/3) : 7.787 * x + 16/116;
    y = y > 0.008856 ? Math.pow(y, 1/3) : 7.787 * y + 16/116;
    z = z > 0.008856 ? Math.pow(z, 1/3) : 7.787 * z + 16/116;

    const lValue = 116 * y - 16;
    const aValue = 500 * (x - y);
    const bValue = 200 * (y - z);

    return { 'l': lValue, 'a': aValue, 'b': bValue };
}

function labDistance(color1, color2) {
    const deltaL = color1.l - color2.l;
    const deltaA = color1.a - color2.a;
    const deltaB = color1.b - color2.b;
    // Weighted Delta E approximation
    return Math.sqrt(0.2 * deltaL * deltaL + 3 * deltaA * deltaA + 3 * deltaB * deltaB);
}

function findClosestColor(r, g, b, paletteMode) {
    if (paletteMode === 'threeColor') {
        // Red extraction bias threshold
        if (r > 120 && r > g * 1.5 && r > b * 1.5) {
            return threeColorPalette[2]; // Return Red
        }
        const gray = 0.299 * r + 0.587 * g + 0.114 * b;
        return gray < 128 ? threeColorPalette[0] : threeColorPalette[1]; // Black or White
    } else {
        const gray = 0.299 * r + 0.587 * g + 0.114 * b;
        return gray < 128 ? blackWhitePalette[0] : blackWhitePalette[1]; // Black or White
    }
}

// --- Image Quantization & Dithering Algorithms ---

const DitherAlgorithms = {
    'floydSteinberg': function(imageData, factor, paletteMode) {
        const width = imageData.width;
        const height = imageData.height;
        const pixels = imageData.data;
        const buffer = new Uint8ClampedArray(pixels);

        for (let y = 0; y < height; y++) {
            for (let x = 0; x < width; x++) {
                const idx = (y * width + x) * 4;
                const r = buffer[idx];
                const g = buffer[idx + 1];
                const b = buffer[idx + 2];

                const closest = findClosestColor(r, g, b, paletteMode);
                const errR = (r - closest.r) * factor;
                const errG = (g - closest.g) * factor;
                const errB = (b - closest.b) * factor;

                if (x + 1 < width) {
                    const nIdx = idx + 4;
                    buffer[nIdx]     = Math.min(255, Math.max(0, buffer[nIdx]     + errR * 7 / 16));
                    buffer[nIdx + 1] = Math.min(255, Math.max(0, buffer[nIdx + 1] + errG * 7 / 16));
                    buffer[nIdx + 2] = Math.min(255, Math.max(0, buffer[nIdx + 2] + errB * 7 / 16));
                }
                if (y + 1 < height) {
                    if (x > 0) {
                        const nIdx = idx + width * 4 - 4;
                        buffer[nIdx]     = Math.min(255, Math.max(0, buffer[nIdx]     + errR * 3 / 16));
                        buffer[nIdx + 1] = Math.min(255, Math.max(0, buffer[nIdx + 1] + errG * 3 / 16));
                        buffer[nIdx + 2] = Math.min(255, Math.max(0, buffer[nIdx + 2] + errB * 3 / 16));
                    }
                    const nIdxCenter = idx + width * 4;
                    buffer[nIdxCenter]     = Math.min(255, Math.max(0, buffer[nIdxCenter]     + errR * 5 / 16));
                    buffer[nIdxCenter + 1] = Math.min(255, Math.max(0, buffer[nIdxCenter + 1] + errG * 5 / 16));
                    buffer[nIdxCenter + 2] = Math.min(255, Math.max(0, buffer[nIdxCenter + 2] + errB * 5 / 16));
                    
                    if (x + 1 < width) {
                        const nIdxRight = idx + width * 4 + 4;
                        buffer[nIdxRight]     = Math.min(255, Math.max(0, buffer[nIdxRight]     + errR * 1 / 16));
                        buffer[nIdxRight + 1] = Math.min(255, Math.max(0, buffer[nIdxRight + 1] + errG * 1 / 16));
                        buffer[nIdxRight + 2] = Math.min(255, Math.max(0, buffer[nIdxRight + 2] + errB * 1 / 16));
                    }
                }
            }
        }

        for (let y = 0; y < height; y++) {
            for (let x = 0; x < width; x++) {
                const idx = (y * width + x) * 4;
                const closest = findClosestColor(buffer[idx], buffer[idx + 1], buffer[idx + 2], paletteMode);
                pixels[idx]     = closest.r;
                pixels[idx + 1] = closest.g;
                pixels[idx + 2] = closest.b;
            }
        }
        return imageData;
    },

    'atkinson': function(imageData, factor, paletteMode) {
        const width = imageData.width;
        const height = imageData.height;
        const pixels = imageData.data;
        const buffer = new Uint8ClampedArray(pixels);
        const errWeight = factor * 1 / 8;

        for (let y = 0; y < height; y++) {
            for (let x = 0; x < width; x++) {
                const idx = (y * width + x) * 4;
                const r = buffer[idx];
                const g = buffer[idx + 1];
                const b = buffer[idx + 2];

                const closest = findClosestColor(r, g, b, paletteMode);
                const errR = (r - closest.r) * errWeight;
                const errG = (g - closest.g) * errWeight;
                const errB = (b - closest.b) * errWeight;

                if (x + 1 < width) {
                    const nIdx = idx + 4;
                    buffer[nIdx]     = Math.min(255, Math.max(0, buffer[nIdx]     + errR));
                    buffer[nIdx + 1] = Math.min(255, Math.max(0, buffer[nIdx + 1] + errG));
                    buffer[nIdx + 2] = Math.min(255, Math.max(0, buffer[nIdx + 2] + errB));
                }
                if (x + 2 < width) {
                    const nIdx = idx + 8;
                    buffer[nIdx]     = Math.min(255, Math.max(0, buffer[nIdx]     + errR));
                    buffer[nIdx + 1] = Math.min(255, Math.max(0, buffer[nIdx + 1] + errG));
                    buffer[nIdx + 2] = Math.min(255, Math.max(0, buffer[nIdx + 2] + errB));
                }
                if (y + 1 < height) {
                    if (x > 0) {
                        const nIdx = idx + width * 4 - 4;
                        buffer[nIdx]     = Math.min(255, Math.max(0, buffer[nIdx]     + errR));
                        buffer[nIdx + 1] = Math.min(255, Math.max(0, buffer[nIdx + 1] + errG));
                        buffer[nIdx + 2] = Math.min(255, Math.max(0, buffer[nIdx + 2] + errB));
                    }
                    const nIdxCenter = idx + width * 4;
                    buffer[nIdxCenter]     = Math.min(255, Math.max(0, buffer[nIdxCenter]     + errR));
                    buffer[nIdxCenter + 1] = Math.min(255, Math.max(0, buffer[nIdxCenter + 1] + errG));
                    buffer[nIdxCenter + 2] = Math.min(255, Math.max(0, buffer[nIdxCenter + 2] + errB));
                    
                    if (x + 1 < width) {
                        const nIdxRight = idx + width * 4 + 4;
                        buffer[nIdxRight]     = Math.min(255, Math.max(0, buffer[nIdxRight]     + errR));
                        buffer[nIdxRight + 1] = Math.min(255, Math.max(0, buffer[nIdxRight + 1] + errG));
                        buffer[nIdxRight + 2] = Math.min(255, Math.max(0, buffer[nIdxRight + 2] + errB));
                    }
                }
            }
        }

        for (let y = 0; y < height; y++) {
            for (let x = 0; x < width; x++) {
                const idx = (y * width + x) * 4;
                const closest = findClosestColor(buffer[idx], buffer[idx + 1], buffer[idx + 2], paletteMode);
                pixels[idx]     = closest.r;
                pixels[idx + 1] = closest.g;
                pixels[idx + 2] = closest.b;
            }
        }
        return imageData;
    },

    'bayer': function(imageData, factor, paletteMode) {
        const width = imageData.width;
        const height = imageData.height;
        const pixels = imageData.data;
        
        const bayerMatrix = [
            [0,  8,  2,  10],
            [12, 4,  14, 6],
            [3,  11, 1,  9],
            [15, 7,  13, 5]
        ];
        const matrixSize = 4;
        const matrixDivisor = 16;

        for (let y = 0; y < height; y++) {
            for (let x = 0; x < width; x++) {
                const idx = (y * width + x) * 4;
                const r = pixels[idx];
                const g = pixels[idx + 1];
                const b = pixels[idx + 2];

                const gray = 0.299 * r + 0.587 * g + 0.114 * b;
                const mX = x % matrixSize;
                const mY = y % matrixSize;
                const thresholdValue = bayerMatrix[mY][mX];

                if (paletteMode === 'threeColor' && r > 120 && r > g * 1.5 && r > b * 1.5) {
                    pixels[idx]     = 255;
                    pixels[idx + 1] = 0;
                    pixels[idx + 2] = 0;
                } else {
                    const threshold = (thresholdValue / matrixDivisor) * 255 * factor;
                    if (gray < 128 + (threshold - 128)) {
                        pixels[idx]     = 0;
                        pixels[idx + 1] = 0;
                        pixels[idx + 2] = 0;
                    } else {
                        pixels[idx]     = 255;
                        pixels[idx + 1] = 255;
                        pixels[idx + 2] = 255;
                    }
                }
            }
        }
        return imageData;
    },

    'stucki': function(imageData, factor, paletteMode) {
        const width = imageData.width;
        const height = imageData.height;
        const pixels = imageData.data;
        const buffer = new Uint8ClampedArray(pixels);
        const errWeight = factor * 1 / 42;

        for (let y = 0; y < height; y++) {
            for (let x = 0; x < width; x++) {
                const idx = (y * width + x) * 4;
                const r = buffer[idx];
                const g = buffer[idx + 1];
                const b = buffer[idx + 2];

                const closest = findClosestColor(r, g, b, paletteMode);
                const errR = (r - closest.r) * errWeight;
                const errG = (g - closest.g) * errWeight;
                const errB = (b - closest.b) * errWeight;

                if (x + 1 < width) {
                    const nIdx = idx + 4;
                    buffer[nIdx]     = Math.min(255, Math.max(0, buffer[nIdx]     + errR * 8));
                    buffer[nIdx + 1] = Math.min(255, Math.max(0, buffer[nIdx + 1] + errG * 8));
                    buffer[nIdx + 2] = Math.min(255, Math.max(0, buffer[nIdx + 2] + errB * 8));
                }
                if (x + 2 < width) {
                    const nIdx = idx + 8;
                    buffer[nIdx]     = Math.min(255, Math.max(0, buffer[nIdx]     + errR * 4));
                    buffer[nIdx + 1] = Math.min(255, Math.max(0, buffer[nIdx + 1] + errG * 4));
                    buffer[nIdx + 2] = Math.min(255, Math.max(0, buffer[nIdx + 2] + errB * 4));
                }
                if (y + 1 < height) {
                    if (x > 1) {
                        const nIdx = idx + width * 4 - 8;
                        buffer[nIdx]     = Math.min(255, Math.max(0, buffer[nIdx]     + errR * 2));
                        buffer[nIdx + 1] = Math.min(255, Math.max(0, buffer[nIdx + 1] + errG * 2));
                        buffer[nIdx + 2] = Math.min(255, Math.max(0, buffer[nIdx + 2] + errB * 2));
                    }
                    if (x > 0) {
                        const nIdx = idx + width * 4 - 4;
                        buffer[nIdx]     = Math.min(255, Math.max(0, buffer[nIdx]     + errR * 4));
                        buffer[nIdx + 1] = Math.min(255, Math.max(0, buffer[nIdx + 1] + errG * 4));
                        buffer[nIdx + 2] = Math.min(255, Math.max(0, buffer[nIdx + 2] + errB * 4));
                    }
                    const nIdxCenter = idx + width * 4;
                    buffer[nIdxCenter]     = Math.min(255, Math.max(0, buffer[nIdxCenter]     + errR * 8));
                    buffer[nIdxCenter + 1] = Math.min(255, Math.max(0, buffer[nIdxCenter + 1] + errG * 8));
                    buffer[nIdxCenter + 2] = Math.min(255, Math.max(0, buffer[nIdxCenter + 2] + errB * 8));
                    
                    if (x + 1 < width) {
                        const nIdxRight = idx + width * 4 + 4;
                        buffer[nIdxRight]     = Math.min(255, Math.max(0, buffer[nIdxRight]     + errR * 4));
                        buffer[nIdxRight + 1] = Math.min(255, Math.max(0, buffer[nIdxRight + 1] + errG * 4));
                        buffer[nIdxRight + 2] = Math.min(255, Math.max(0, buffer[nIdxRight + 2] + errB * 4));
                    }
                    if (x + 2 < width) {
                        const nIdxFarRight = idx + width * 4 + 8;
                        buffer[nIdxFarRight]     = Math.min(255, Math.max(0, buffer[nIdxFarRight]     + errR * 2));
                        buffer[nIdxFarRight + 1] = Math.min(255, Math.max(0, buffer[nIdxFarRight + 1] + errG * 2));
                        buffer[nIdxFarRight + 2] = Math.min(255, Math.max(0, buffer[nIdxFarRight + 2] + errB * 2));
                    }
                }
            }
        }

        for (let y = 0; y < height; y++) {
            for (let x = 0; x < width; x++) {
                const idx = (y * width + x) * 4;
                const closest = findClosestColor(buffer[idx], buffer[idx + 1], buffer[idx + 2], paletteMode);
                pixels[idx]     = closest.r;
                pixels[idx + 1] = closest.g;
                pixels[idx + 2] = closest.b;
            }
        }
        return imageData;
    },

    'jarvis': function(imageData, factor, paletteMode) {
        const width = imageData.width;
        const height = imageData.height;
        const pixels = imageData.data;
        const buffer = new Uint8ClampedArray(pixels);
        const errWeight = factor * 1 / 48;

        for (let y = 0; y < height; y++) {
            for (let x = 0; x < width; x++) {
                const idx = (y * width + x) * 4;
                const r = buffer[idx];
                const g = buffer[idx + 1];
                const b = buffer[idx + 2];

                const closest = findClosestColor(r, g, b, paletteMode);
                const errR = (r - closest.r) * errWeight;
                const errG = (g - closest.g) * errWeight;
                const errB = (b - closest.b) * errWeight;

                if (x + 1 < width) {
                    const nIdx = idx + 4;
                    buffer[nIdx]     = Math.min(255, Math.max(0, buffer[nIdx]     + errR * 7));
                    buffer[nIdx + 1] = Math.min(255, Math.max(0, buffer[nIdx + 1] + errG * 7));
                    buffer[nIdx + 2] = Math.min(255, Math.max(0, buffer[nIdx + 2] + errB * 7));
                }
                if (x + 2 < width) {
                    const nIdx = idx + 8;
                    buffer[nIdx]     = Math.min(255, Math.max(0, buffer[nIdx]     + errR * 5));
                    buffer[nIdx + 1] = Math.min(255, Math.max(0, buffer[nIdx + 1] + errG * 5));
                    buffer[nIdx + 2] = Math.min(255, Math.max(0, buffer[nIdx + 2] + errB * 5));
                }
                if (y + 1 < height) {
                    if (x > 1) {
                        const nIdx = idx + width * 4 - 8;
                        buffer[nIdx]     = Math.min(255, Math.max(0, buffer[nIdx]     + errR * 3));
                        buffer[nIdx + 1] = Math.min(255, Math.max(0, buffer[nIdx + 1] + errG * 3));
                        buffer[nIdx + 2] = Math.min(255, Math.max(0, buffer[nIdx + 2] + errB * 3));
                    }
                    if (x > 0) {
                        const nIdx = idx + width * 4 - 4;
                        buffer[nIdx]     = Math.min(255, Math.max(0, buffer[nIdx]     + errR * 5));
                        buffer[nIdx + 1] = Math.min(255, Math.max(0, buffer[nIdx + 1] + errG * 5));
                        buffer[nIdx + 2] = Math.min(255, Math.max(0, buffer[nIdx + 2] + errB * 5));
                    }
                    const nIdxCenter = idx + width * 4;
                    buffer[nIdxCenter]     = Math.min(255, Math.max(0, buffer[nIdxCenter]     + errR * 7));
                    buffer[nIdxCenter + 1] = Math.min(255, Math.max(0, buffer[nIdxCenter + 1] + errG * 7));
                    buffer[nIdxCenter + 2] = Math.min(255, Math.max(0, buffer[nIdxCenter + 2] + errB * 7));
                    
                    if (x + 1 < width) {
                        const nIdxRight = idx + width * 4 + 4;
                        buffer[nIdxRight]     = Math.min(255, Math.max(0, buffer[nIdxRight]     + errR * 5));
                        buffer[nIdxRight + 1] = Math.min(255, Math.max(0, buffer[nIdxRight + 1] + errG * 5));
                        buffer[nIdxRight + 2] = Math.min(255, Math.max(0, buffer[nIdxRight + 2] + errB * 5));
                    }
                    if (x + 2 < width) {
                        const nIdxFarRight = idx + width * 4 + 8;
                        buffer[nIdxFarRight]     = Math.min(255, Math.max(0, buffer[nIdxFarRight]     + errR * 3));
                        buffer[nIdxFarRight + 1] = Math.min(255, Math.max(0, buffer[nIdxFarRight + 1] + errG * 3));
                        buffer[nIdxFarRight + 2] = Math.min(255, Math.max(0, buffer[nIdxFarRight + 2] + errB * 3));
                    }
                }
                if (y + 2 < height) {
                    if (x > 1) {
                        const nIdx = idx + width * 4 * 2 - 8;
                        buffer[nIdx]     = Math.min(255, Math.max(0, buffer[nIdx]     + errR * 1));
                        buffer[nIdx + 1] = Math.min(255, Math.max(0, buffer[nIdx + 1] + errG * 1));
                        buffer[nIdx + 2] = Math.min(255, Math.max(0, buffer[nIdx + 2] + errB * 1));
                    }
                    if (x > 0) {
                        const nIdx = idx + width * 4 * 2 - 4;
                        buffer[nIdx]     = Math.min(255, Math.max(0, buffer[nIdx]     + errR * 3));
                        buffer[nIdx + 1] = Math.min(255, Math.max(0, buffer[nIdx + 1] + errG * 3));
                        buffer[nIdx + 2] = Math.min(255, Math.max(0, buffer[nIdx + 2] + errB * 3));
                    }
                    const nIdxCenter = idx + width * 4 * 2;
                    buffer[nIdxCenter]     = Math.min(255, Math.max(0, buffer[nIdxCenter]     + errR * 5));
                    buffer[nIdxCenter + 1] = Math.min(255, Math.max(0, buffer[nIdxCenter + 1] + errG * 5));
                    buffer[nIdxCenter + 2] = Math.min(255, Math.max(0, buffer[nIdxCenter + 2] + errB * 5));
                    
                    if (x + 1 < width) {
                        const nIdxRight = idx + width * 4 * 2 + 4;
                        buffer[nIdxRight]     = Math.min(255, Math.max(0, buffer[nIdxRight]     + errR * 3));
                        buffer[nIdxRight + 1] = Math.min(255, Math.max(0, buffer[nIdxRight + 1] + errG * 3));
                        buffer[nIdxRight + 2] = Math.min(255, Math.max(0, buffer[nIdxRight + 2] + errB * 3));
                    }
                    if (x + 2 < width) {
                        const nIdxFarRight = idx + width * 4 * 2 + 8;
                        buffer[nIdxFarRight]     = Math.min(255, Math.max(0, buffer[nIdxFarRight]     + errR * 1));
                        buffer[nIdxFarRight + 1] = Math.min(255, Math.max(0, buffer[nIdxFarRight + 1] + errG * 1));
                        buffer[nIdxFarRight + 2] = Math.min(255, Math.max(0, buffer[nIdxFarRight + 2] + errB * 1));
                    }
                }
            }
        }

        for (let y = 0; y < height; y++) {
            for (let x = 0; x < width; x++) {
                const idx = (y * width + x) * 4;
                const closest = findClosestColor(buffer[idx], buffer[idx + 1], buffer[idx + 2], paletteMode);
                pixels[idx]     = closest.r;
                pixels[idx + 1] = closest.g;
                pixels[idx + 2] = closest.b;
            }
        }
        return imageData;
    }
};

// --- Fallback Standard Floyd-Steinberg Function ---
function floydSteinbergDither(imageData, factor, paletteMode) {
    return DitherAlgorithms['floydSteinberg'](imageData, factor, paletteMode);
}

// --- Image Processing Chain Coordinator ---
function processImage1(sourceData, brightness, contrast, saturation, diffusionFactor, paletteMode, algorithmName) {
    const outputData = new ImageData(new Uint8ClampedArray(sourceData.data), sourceData.width, sourceData.height);
    
    adjustBrightness(outputData, brightness);
    adjustContrast(outputData, contrast);
    adjustSaturation(outputData, saturation);
    
    if (DitherAlgorithms[algorithmName]) {
        DitherAlgorithms[algorithmName](outputData, diffusionFactor, paletteMode);
    } else {
        floydSteinbergDither(outputData, diffusionFactor, paletteMode);
    }
    
    return outputData;
}

// --- Raw Binary Conversion for E-Ink Displays (EPD) ---
function imageDataToEpdBytes(imageData, paletteMode) {
    const width = imageData.width;
    const height = imageData.height;
    const pixels = imageData.data;
    let epdBuffer;

    if (paletteMode === 'threeColor') {
        // Generates 2 bitstreams combined (Layer 1: Black/White, Layer 2: Red)
        const totalBytesPerLayer = Math.ceil(width * height / 8);
        epdBuffer = new Uint8Array(totalBytesPerLayer * 2);
        
        let bwIdx = 0;
        let redIdx = totalBytesPerLayer;
        let bitCounter = 0;
        let currentBwByte = 0;
        let currentRedByte = 0;

        for (let i = 0; i < pixels.length; i += 4) {
            const r = pixels[i];
            const g = pixels[i + 1];
            const b = pixels[i + 2];

            const isRed = (r > 200 && g < 50 && b < 50);
            const isBlack = !isRed && (0.299 * r + 0.587 * g + 0.114 * b < 128);

            if (isBlack) currentBwByte  |= (1 << (7 - bitCounter));
            if (isRed)   currentRedByte |= (1 << (7 - bitCounter));

            bitCounter++;
            if (bitCounter === 8) {
                epdBuffer[bwIdx++] = currentBwByte;
                epdBuffer[redIdx++] = currentRedByte;
                bitCounter = 0;
                currentBwByte = 0;
                currentRedByte = 0;
            }
        }
        if (bitCounter > 0) {
            epdBuffer[bwIdx] = currentBwByte;
            epdBuffer[redIdx] = currentRedByte;
        }
    } else {
        // Standard 1-bit Black and White bit packing
        epdBuffer = new Uint8Array(Math.ceil(width * height / 8));
        let byteIdx = 0;
        let bitCounter = 0;
        let currentByte = 0;

        for (let i = 0; i < pixels.length; i += 4) {
            const r = pixels[i];
            const g = pixels[i + 1];
            const b = pixels[i + 2];
            const isBlack = (0.299 * r + 0.587 * g + 0.114 * b < 128);

            if (isBlack) {
                currentByte |= (1 << (7 - bitCounter));
            }

            bitCounter++;
            if (bitCounter === 8) {
                epdBuffer[byteIdx++] = currentByte;
                bitCounter = 0;
                currentByte = 0;
            }
        }
        if (bitCounter > 0) {
            epdBuffer[byteIdx] = currentByte;
        }
    }
    return epdBuffer;
}

// --- DOM Binding & Interface Controls ---
const imageUpload = document.getElementById('imageUpload');
const previewCanvas = document.getElementById('previewCanvas');
const floatPreviewCanvas = document.getElementById('floatPreviewCanvas');
const noImagePlaceholder = document.getElementById('noImagePlaceholder');
const processedImageInfo = document.getElementById('processedImageInfo');
const btnProcess = document.getElementById('btnProcess');
const btnSend = document.getElementById('btnSend');
const btnDownload = document.getElementById('btnDownload');
const btnReset = document.getElementById('btnReset');
const btnClearLog = document.getElementById('btnClearLog');
const btnBlackWhite = document.getElementById('btnBlackWhite');
const btnBlackWhiteRed = document.getElementById('btnBlackWhiteRed');
const ditherMode = document.getElementById('ditherMode');
const ditherAlg = document.getElementById('ditherAlg');
const logContainer = document.getElementById('logContainer');
const statusContainer = document.getElementById('statusContainer');
const floatingCanvasContainer = document.getElementById('floatingCanvasContainer');
const toggleCanvasFloat = document.getElementById('toggleCanvasFloat');
const closeCanvas = document.getElementById('closeCanvas');
const canvasResizeHandle = document.getElementById('canvasResizeHandle');
const imageScaleSlider = document.getElementById('imageScaleSlider');
const imageScaleValue = document.getElementById('imageScaleValue');
const addTextBtn = document.getElementById('addTextBtn');
const timeDialog = document.getElementById('timeDialog');
const datetimeInput = document.getElementById('datetimeInput');
const closeTimeDialog = document.getElementById('closeTimeDialog');
const confirmTimeBtn = document.getElementById('confirmTimeBtn');
const imageWidthInput = document.getElementById('imageWidthInput');
const imageHeightInput = document.getElementById('imageHeightInput');
const toolPen = document.getElementById('toolPen');
const toolEraser = document.getElementById('toolEraser');
const toolText = document.getElementById('toolText');
const toolClear = document.getElementById('toolClear');
const brushSizeSlider = document.getElementById('brushSizeSlider');
const fontSizeInput = document.getElementById('fontSizeInput');
const fontFamilySelect = document.getElementById('fontFamilySelect');
const textInput = document.getElementById('textInput');
const drawingStatus = document.getElementById('drawingStatus');
const currentToolEl = document.getElementById('currentTool');
const currentSizeEl = document.getElementById('currentSize');
const drawingModeIndicator = document.getElementById('drawingModeIndicator');
const toggleDrawingModeBtn = document.getElementById('toggleDrawingModeBtn');
const floatToggleDrawingModeBtn = document.getElementById('floatToggleDrawingModeBtn');

const sliders = {
    'saturation': document.getElementById('saturationSlider'),
    'brightness': document.getElementById('brightnessSlider'),
    'contrast': document.getElementById('contrastSlider'),
    'diffusion': document.getElementById('diffusionSlider')
};

const ditherSlider = document.getElementById('ditherSlider');

const sliderValues = {
    'saturation': document.getElementById('saturationValue'),
    'brightness': document.getElementById('brightnessValue'),
    'contrast': document.getElementById('contrastValue'),
    'diffusion': document.getElementById('diffusionValue')
};

// --- Initialization Subsystem ---
function init() {
    canvas = previewCanvas;
    ctx = canvas.getContext('2d');
    floatCanvas = floatPreviewCanvas;
    floatCtx = floatCanvas.getContext('2d');
    
    updateCanvasSize();

    // Auto-calculate current localized ISO timestamp configurations
    const now = new Date();
    const localizedTime = new Date(now.getTime() - now.getTimezoneOffset() * 60000).toISOString().substring(0, 16);
    datetimeInput.value = localizedTime;

    // Interface Canvas drawing interaction listeners
    canvas.addEventListener('mousedown', startDrawing);
    canvas.addEventListener('mousemove', draw);
    canvas.addEventListener('mouseup', stopDrawing);
    canvas.addEventListener('mouseout', stopDrawing);

    floatCanvas.addEventListener('mousedown', startDrawingFloat);
    floatCanvas.addEventListener('mousemove', drawFloat);
    // [Truncated snippet ends here...]
}