/* â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•
 * splat_convert.js â€” Gaussian Splat format converter, pure browser JS.
 *
 * Faithful port of format_converter/converter.py (Python/numpy) so the
 * No_LocalServer build can convert without the FastAPI backend.
 *
 * Formats: .ply  .compressed.ply  .splat  .ksplat  .spz  .sog  .glb
 * Requires: globalThis.JSZip (sog zip), globalThis.fzstd (spz v4 read) â€” from bundle.js.
 * Browser APIs: CompressionStream/DecompressionStream ('gzip', 'deflate'),
 *               createImageBitmap + OffscreenCanvas (sog image decode).
 *
 * Deviations from the Python reference (documented):
 *  - SPZ write: gzip level is the browser default (CompressionStream has no
 *    level parameter) instead of a 1-9 choice.
 *  - SPZ colors use Niantic colorScale=0.15 on SH DC (not SH_C0 display RGB).
 *  - detectFormatFromBytes sniffs content first so a leftover `.spz` name on
 *    rewritten compressed-PLY blobs cannot passthrough and wash colors.
 *  - SPZ decode is raw (no axis flip), matching @playcanvas/splat-transform and
 *    SuperSplat: files are authored in PLY/RDF space (Transform.PLY). Legacy
 *    Niantic RUB conversion is NOT applied — SuperSplat .spz would flip upside-down.
 *  - Compressed PLY chunk min_r…max_b are PlayCanvas *display-linear*
 *    (f_dc * SH_C0 + 0.5), not raw f_dc.  GS3D / SuperSplat loaders treat
 *    them as display and skip a second SH_C0.  Our cloud always stores f_dc.
 *  - SOG write: images are encoded as lossless PNG bytes but keep the
 *    canonical *.webp names from the SOG spec.  Canvas WebP encoding
 *    premultiplies alpha which corrupts data channels (sh0 stores codebook
 *    indices in RGB with opacity in A); a pure-JS PNG encoder is exact.
 *    Every real SOG consumer (browsers, PIL, PlayCanvas engine) sniffs the
 *    actual image bytes rather than trusting the extension.
 *  - Big-endian PLY input is rejected (vanishingly rare).
 *
 * Cloud representation (mirrors GaussianCloud):
 *   { count, positions F32(N*3), scales F32(N*3) log-scale,
 *     rotations F32(N*4) wxyz, opacities F32(N) logit, shDc F32(N*3),
 *     shRest: F32(N*K)|null, shK: K, normals F32(N*3)|null, mr F32(N*2)|null }
 *
 * Per-format color / opacity / scale conventions (writers):
 *   .ply            f_dc as float; opacity logit; scale log (INRIA 3DGS)
 *   .compressed.ply chunk colors = display (SH_C0); opacity sigmoid→u8;
 *                   scale log in chunk min/max; SH rest uchar → ±4 range
 *   .splat/.ksplat  display RGB u8 via SH_C0; opacity sigmoid→u8; scale linear
 *   .spz            f_dc via colorScale=0.15; opacity sigmoid→u8; scale
 *                   (log+10)*16; positions/rots raw (PLY space, no 180° X)
 *   .sog            sh0 codebook = f_dc; scales codebook = log; opacity u8
 *   .glb (KHR GS)   SH_DEGREE_0 = f_dc; OPACITY linear; SCALE linear; 180° X
 *
 * Color space: no sRGB/gamma encode on export. Loaders consume SH_C0 display-
 * linear RGB directly; pow(c, 1/2.2) would wash or crush colors.
 * Scale floor on linear→log reads is 1e-20 (not 1e-10) so flat axes stay flat.
 * â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â• */
'use strict';

(function () {

const SH_C0 = 0.28209479177387814;
const SPZ_MAGIC = 0x5053474e;            // "NGSP" little-endian
const SPZ_DEFAULT_FRAC_BITS = 12;
/** Niantic SPZ DC color pack: byte = f_dc * colorScale * 255 + 0.5*255 (NOT SH_C0 display RGB). */
const SPZ_COLOR_SCALE = 0.15;
const spzShDcToByte = (fdc) => clamp(Math.round(fdc * SPZ_COLOR_SCALE * 255 + 0.5 * 255), 0, 255);
const spzByteToShDc = (b) => (b / 255 - 0.5) / SPZ_COLOR_SCALE;
const SPLAT_ROW_BYTES = 32;
const CPLY_CHUNK_SIZE = 256;

/** PlayCanvas / SuperSplat: chunk rows cover ceil(N / chunkSize) splats in file order. */
function compressedPlyVerticesPerChunk(vertexCount, chunkCount) {
  const N = vertexCount | 0;
  const C = chunkCount | 0;
  if (C <= 0 || N <= 0) return CPLY_CHUNK_SIZE;
  return Math.max(1, Math.ceil(N / C));
}
const SH_REST_COUNT = { 0: 0, 1: 9, 2: 24, 3: 45 };
const KSPLAT_HEADER_BYTES  = 4096;
const KSPLAT_SECTION_BYTES = 1024;
const KSPLAT_BYTES_PER_SPLAT = 44;
const SQRT2 = Math.SQRT2;

/* â”€â”€â”€ Small helpers â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€ */

/* ── Color / scale / axis helpers (canonical cloud ↔ on-disk) ───────────────
 *
 * Cloud always stores:
 *   shDc      = raw f_dc_0…2  (INRIA SH DC)
 *   scales    = log(linear)   (INRIA scale_0…2)
 *   rotations = wxyz unit quat
 *   opacities = logit(alpha)
 *
 * Display-linear RGB (what .splat / .ksplat / compressed-PLY chunks store):
 *   R = 0.5 + SH_C0 * f_dc_0     (SH_C0 = 0.28209479177387814 = 1/(2√π))
 *   same for G/B.  May be outside [0,1] (PlayCanvas HDR); uint8 targets clamp.
 *
 * Do NOT apply sRGB/gamma (pow 1/2.2).  3DGS loaders (GS3D, antimatter15,
 * PlayCanvas) treat the SH_C0 mapping as the final display RGB — a gamma pass
 * would wash or crush colors.
 */

const clamp = (v, lo, hi) => v < lo ? lo : (v > hi ? hi : v);
const sigmoid = x => 1 / (1 + Math.exp(-x));
function logit(p) { p = clamp(p, 1e-6, 1 - 1e-6); return Math.log(p / (1 - p)); }

/** f_dc → display-linear (unclamped; may be outside [0,1]). */
const shDcToDisplay = (fdc) => 0.5 + SH_C0 * fdc;
/** display-linear → f_dc. */
const rgbToShDc = (rgb) => (rgb - 0.5) / SH_C0;
/** Clamped [0,1] display for uint8 formats (.splat / .ksplat). */
const shDcToRgb = (fdc) => clamp(shDcToDisplay(fdc), 0, 1);
/** Pack one f_dc channel to uint8 display RGB. */
const packShDcToU8 = (fdc) => clamp(Math.round(shDcToRgb(fdc) * 255), 0, 255);
/** Unpack uint8 display RGB → f_dc. */
const unpackU8ToShDc = (b) => rgbToShDc(b / 255);

/**
 * Linear scale ↔ log scale.  Floor is tiny (≈e^-46) so anisotropic "flat"
 * Gaussians are not forced up to 1e-10 and puffed into needles on re-export.
 * Writers use logScaleToLinear with no artificial minimum inflate.
 */
const LOG_SCALE_FLOOR = 1e-20; // Math.log(1e-20) ≈ -46.05
function linearScaleToLog(lin) {
  const v = +lin;
  if (!Number.isFinite(v) || v <= 0) return Math.log(LOG_SCALE_FLOOR);
  return Math.log(Math.max(v, LOG_SCALE_FLOOR));
}
function logScaleToLinear(logS) {
  const v = +logS;
  if (!Number.isFinite(v)) return LOG_SCALE_FLOOR;
  return Math.exp(v);
}

/**
 * 180° rotation about X: (x,y,z) → (x,−y,−z).
 * Quaternion (w,x,y,z) → (w,x,−y,−z) — conjugate of the same half-turn,
 * not an index shuffle.  Used by SPZ (RUB) and KHR_gaussian_splatting (Y-up).
 */
function apply180XPos(x, y, z) { return [x, -y, -z]; }
function apply180XQuatWxyz(w, x, y, z) { return [w, x, -y, -z]; }

/** Contiguous Uint8Array — avoids misaligned/incorrect views from Node Buffer. */
function ensureBytes(bytes) {
  if (typeof Buffer !== 'undefined' && typeof Buffer.isBuffer === 'function' && Buffer.isBuffer(bytes))
    return new Uint8Array(bytes);
  if (bytes instanceof Uint8Array && bytes.byteOffset === 0 && bytes.byteLength === bytes.buffer.byteLength)
    return bytes;
  return new Uint8Array(bytes);
}

/** PlayCanvas compressed PLY: uchar SH rest → float f_rest (matches gaussian-splats-3d). */
function cplyShByteToFloat(b) { return b * (8 / 255) - 4; }
function cplyShFloatToByte(v) { return clamp(Math.round((v + 4) * 255 / 8), 0, 255); }

const unpack111011 = (v) => ({
  x: ((v >>> 21) & 2047) / 2047,
  y: ((v >>> 11) & 1023) / 1023,
  z: (v & 2047) / 2047,
});

function makeCloud(N) {
  return {
    count: N,
    positions: new Float32Array(N * 3),
    scales:    new Float32Array(N * 3),
    rotations: new Float32Array(N * 4),
    opacities: new Float32Array(N),
    shDc:      new Float32Array(N * 3),
    shRest:    null, shK: 0,
    normals:   null, mr: null,
  };
}

function normalizeRotations(c) {
  const r = c.rotations;
  for (let i = 0; i < c.count; i++) {
    const o = i * 4;
    const n = Math.hypot(r[o], r[o+1], r[o+2], r[o+3]);
    const inv = 1 / Math.max(n, 1e-8);
    r[o] *= inv; r[o+1] *= inv; r[o+2] *= inv; r[o+3] *= inv;
  }
}

function cloudShDegree(c) {
  if (!c.shRest || c.shK === 0) return 0;
  for (const d of [3, 2, 1]) if (c.shK >= SH_REST_COUNT[d]) return d;
  return 0;
}

function truncateSh(c, maxDegree) {
  if (maxDegree >= 3 || !c.shRest || c.shK === 0) return;
  const target = SH_REST_COUNT[Math.max(0, maxDegree)] || 0;
  if (target === 0) { c.shRest = null; c.shK = 0; return; }
  if (c.shK > target) {
    const out = new Float32Array(c.count * target);
    for (let i = 0; i < c.count; i++)
      for (let k = 0; k < target; k++) out[i * target + k] = c.shRest[i * c.shK + k];
    c.shRest = out; c.shK = target;
  }
}

/**
 * Cap per-splat linear scale anisotropy for 3DGS viewers (GS3D).
 * SuperSplat / 2DGS-trained scenes often have max/min ≫ 1e4 (paper-thin axes).
 * PlayCanvas renders those as disks; GS3D projects edge-on disks as needles.
 * Raises each axis to at least maxAxis/maxAniso (log-scale cloud in-place).
 */
function clampCloudAnisotropy(c, maxAniso = 8) {
  const lim = Math.max(1, +maxAniso || 8);
  const inv = 1 / lim;
  const N = c.count | 0;
  const sc = c.scales;
  // Absolute floor (~0.1mm if scene is ~meters) so GS3D eigen falloff does not
  // collapse flat axes into zero-width needles even when maxAxis is tiny.
  const ABS_FLOOR = 1e-4;
  for (let i = 0; i < N; i++) {
    const o = i * 3;
    const e0 = Math.exp(sc[o]), e1 = Math.exp(sc[o + 1]), e2 = Math.exp(sc[o + 2]);
    const mx = Math.max(e0, e1, e2, ABS_FLOOR);
    if (!Number.isFinite(mx)) continue;
    const floor = Math.max(mx * inv, ABS_FLOOR);
    sc[o]     = Math.log(Math.max(e0, floor));
    sc[o + 1] = Math.log(Math.max(e1, floor));
    sc[o + 2] = Math.log(Math.max(e2, floor));
  }
  return c;
}

/* int24 packing (SPZ positions) */
function packInt24(values /* Int32Array */) {
  const out = new Uint8Array(values.length * 3);
  for (let i = 0; i < values.length; i++) {
    let v = values[i];
    if (v < 0) v &= 0xFFFFFF;
    out[i*3]   =  v        & 0xFF;
    out[i*3+1] = (v >> 8)  & 0xFF;
    out[i*3+2] = (v >> 16) & 0xFF;
  }
  return out;
}
function unpackInt24(buf /* Uint8Array */, count) {
  const out = new Int32Array(count);
  for (let i = 0; i < count; i++) {
    const u = buf[i*3] | (buf[i*3+1] << 8) | (buf[i*3+2] << 16);
    out[i] = u >= 0x800000 ? u - 0x1000000 : u;
  }
  return out;
}

/* Morton (Z-order) sort indices â€” 10 bits per axis, matches converter.py */
function mortonOrder(positions, N) {
  let mnx = Infinity, mny = Infinity, mnz = Infinity;
  let mxx = -Infinity, mxy = -Infinity, mxz = -Infinity;
  for (let i = 0; i < N; i++) {
    const x = positions[i*3], y = positions[i*3+1], z = positions[i*3+2];
    if (x < mnx) mnx = x; if (x > mxx) mxx = x;
    if (y < mny) mny = y; if (y > mxy) mxy = y;
    if (z < mnz) mnz = z; if (z > mxz) mxz = z;
  }
  const rx = Math.max(mxx - mnx, 1e-12), ry = Math.max(mxy - mny, 1e-12), rz = Math.max(mxz - mnz, 1e-12);
  const spread = v => {
    v = (v | (v << 16)) & 0x030000FF;
    v = (v | (v << 8))  & 0x0300F00F;
    v = (v | (v << 4))  & 0x030C30C3;
    v = (v | (v << 2))  & 0x09249249;
    return v >>> 0;
  };
  const code = new Float64Array(N);   // codes < 2^32 â€” exact in doubles
  for (let i = 0; i < N; i++) {
    const qx = clamp(Math.round((positions[i*3]   - mnx) / rx * 1023), 0, 1023);
    const qy = clamp(Math.round((positions[i*3+1] - mny) / ry * 1023), 0, 1023);
    const qz = clamp(Math.round((positions[i*3+2] - mnz) / rz * 1023), 0, 1023);
    code[i] = spread(qx) * 4 + spread(qy) * 2 + spread(qz);
  }
  const order = new Uint32Array(N);
  for (let i = 0; i < N; i++) order[i] = i;
  return order.sort((a, b) => code[a] - code[b]);   // typed-array sort is fine (numeric)
}

/* Reorder helper: gather rows of a strided array */
function gatherRows(src, order, stride) {
  const out = new Float32Array(order.length * stride);
  for (let i = 0; i < order.length; i++) {
    const s = order[i] * stride, d = i * stride;
    for (let k = 0; k < stride; k++) out[d + k] = src[s + k];
  }
  return out;
}

/** wxyz quaternion multiply: out = a * b */
function quatMulWxyz(a, b) {
  const aw = a[0], ax = a[1], ay = a[2], az = a[3];
  const bw = b[0], bx = b[1], by = b[2], bz = b[3];
  return [
    aw * bw - ax * bx - ay * by - az * bz,
    aw * bx + ax * bw + ay * bz - az * by,
    aw * by - ax * bz + ay * bw + az * bx,
    aw * bz + ax * by - ay * bx + az * bw,
  ];
}

function quatNormalizeWxyz(q) {
  const n = Math.hypot(q[0], q[1], q[2], q[3]) || 1;
  return [q[0] / n, q[1] / n, q[2] / n, q[3] / n];
}

/** Decompose a column-major 4×4 matrix (THREE.js layout). */
function decomposeMatrix4(m16) {
  const tx = m16[12], ty = m16[13], tz = m16[14];
  let sx = Math.hypot(m16[0], m16[1], m16[2]);
  const sy = Math.hypot(m16[4], m16[5], m16[6]);
  const sz = Math.hypot(m16[8], m16[9], m16[10]);
  const det =
    m16[0] * (m16[5] * m16[10] - m16[6] * m16[9]) -
    m16[1] * (m16[4] * m16[10] - m16[6] * m16[8]) +
    m16[2] * (m16[4] * m16[9] - m16[5] * m16[8]);
  let lsx = sx, lsy = sy, lsz = sz;
  if (det < 0) lsx = -lsx;
  const invX = 1 / (Math.abs(lsx) || 1e-12);
  const invY = 1 / (Math.abs(lsy) || 1e-12);
  const invZ = 1 / (Math.abs(lsz) || 1e-12);
  const r00 = m16[0] * invX, r01 = m16[4] * invY, r02 = m16[8] * invZ;
  const r10 = m16[1] * invX, r11 = m16[5] * invY, r12 = m16[9] * invZ;
  const r20 = m16[2] * invX, r21 = m16[6] * invY, r22 = m16[10] * invZ;
  const tr = r00 + r11 + r22;
  let qw, qx, qy, qz;
  if (tr > 0) {
    const s = Math.sqrt(tr + 1) * 2;
    qw = 0.25 * s;
    qx = (r21 - r12) / s;
    qy = (r02 - r20) / s;
    qz = (r10 - r01) / s;
  } else if (r00 > r11 && r00 > r22) {
    const s = Math.sqrt(1 + r00 - r11 - r22) * 2;
    qw = (r21 - r12) / s;
    qx = 0.25 * s;
    qy = (r01 + r10) / s;
    qz = (r02 + r20) / s;
  } else if (r11 > r22) {
    const s = Math.sqrt(1 + r11 - r00 - r22) * 2;
    qw = (r02 - r20) / s;
    qx = (r01 + r10) / s;
    qy = 0.25 * s;
    qz = (r12 + r21) / s;
  } else {
    const s = Math.sqrt(1 + r22 - r00 - r11) * 2;
    qw = (r10 - r01) / s;
    qx = (r02 + r20) / s;
    qy = (r12 + r21) / s;
    qz = 0.25 * s;
  }
  const qn = quatNormalizeWxyz([qw, qx, qy, qz]);
  return {
    tx, ty, tz,
    sx: Math.abs(lsx), sy: Math.abs(lsy), sz: Math.abs(lsz),
    qw: qn[0], qx: qn[1], qy: qn[2], qz: qn[3],
  };
}

/**
 * Apply a rigid/affine transform to every Gaussian in a cloud.
 * Positions, orientations (wxyz), and log-scales are updated.
 * Higher-order SH bands are not rotated (view-dependent tint may shift on large rotations).
 * @param {object} c Gaussian cloud
 * @param {ArrayLike<number>} m16 column-major 4×4 (THREE.Matrix4.elements layout)
 */
function transformCloud(c, m16) {
  if (!c || !c.count) return c;
  const { sx, sy, sz, qw, qx, qy, qz } = decomposeMatrix4(m16);
  const asx = Math.abs(sx) || 1, asy = Math.abs(sy) || 1, asz = Math.abs(sz) || 1;
  const logSx = Math.log(asx), logSy = Math.log(asy), logSz = Math.log(asz);
  const qm = [qw, qx, qy, qz];
  const pos = c.positions, rot = c.rotations, scl = c.scales;
  const n = c.count;
  for (let i = 0; i < n; i++) {
    const x = pos[i * 3], y = pos[i * 3 + 1], z = pos[i * 3 + 2];
    pos[i * 3]     = m16[0] * x + m16[4] * y + m16[8]  * z + m16[12];
    pos[i * 3 + 1] = m16[1] * x + m16[5] * y + m16[9]  * z + m16[13];
    pos[i * 3 + 2] = m16[2] * x + m16[6] * y + m16[10] * z + m16[14];
    const ql = [rot[i * 4], rot[i * 4 + 1], rot[i * 4 + 2], rot[i * 4 + 3]];
    const qr = quatNormalizeWxyz(quatMulWxyz(qm, ql));
    rot[i * 4] = qr[0]; rot[i * 4 + 1] = qr[1]; rot[i * 4 + 2] = qr[2]; rot[i * 4 + 3] = qr[3];
    scl[i * 3] += logSx; scl[i * 3 + 1] += logSy; scl[i * 3 + 2] += logSz;
  }
  normalizeRotations(c);
  return c;
}

/* gzip / gunzip via native streams */
async function gzipBytes(u8) {
  const cs = new CompressionStream('gzip');
  const ab = await new Response(new Blob([u8]).stream().pipeThrough(cs)).arrayBuffer();
  return new Uint8Array(ab);
}
async function gunzipBytes(u8) {
  const ds = new DecompressionStream('gzip');
  const ab = await new Response(new Blob([u8]).stream().pipeThrough(ds)).arrayBuffer();
  return new Uint8Array(ab);
}
async function zlibBytes(u8) {        // zlib container (for PNG IDAT)
  const cs = new CompressionStream('deflate');
  const ab = await new Response(new Blob([u8]).stream().pipeThrough(cs)).arrayBuffer();
  return new Uint8Array(ab);
}

/* â”€â”€â”€ PLY â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€ */

const PLY_TYPE_SIZE = {
  float: 4, float32: 4, double: 8, float64: 8,
  int: 4, int32: 4, uint: 4, uint32: 4,
  short: 2, int16: 2, ushort: 2, uint16: 2,
  char: 1, int8: 1, uchar: 1, uint8: 1,
};

function parsePlyHeader(bytes) {
  // Find end_header
  const probe = new TextDecoder('ascii').decode(bytes.subarray(0, Math.min(bytes.length, 65536)));
  let tag = 'end_header\r\n', idx = probe.indexOf(tag);
  if (idx < 0) { tag = 'end_header\n'; idx = probe.indexOf(tag); }
  if (idx < 0) throw new Error('Malformed PLY: missing end_header');
  const hdrEnd = idx + tag.length;
  const lines = probe.slice(0, hdrEnd).split(/\r?\n/).map(l => l.trim());
  return { lines, hdrEnd };
}

function readPly(bytes) {
  const { lines, hdrEnd } = parsePlyHeader(bytes);
  let N = 0, inVertex = false, isBinary = false;
  const props = [];   // [type, name]
  for (const line of lines) {
    if (line.startsWith('format binary_little_endian')) isBinary = true;
    else if (line.startsWith('format binary_big_endian'))
      throw new Error('Big-endian PLY not supported in the browser converter');
    else if (line.startsWith('format ascii'))
      throw new Error('ASCII PLY not supported; save as binary PLY');
    else if (line.startsWith('element vertex')) { N = parseInt(line.split(/\s+/).pop(), 10); inVertex = true; }
    else if (line.startsWith('element') && inVertex) inVertex = false;
    else if (line.startsWith('property') && inVertex && !line.includes('list')) {
      const p = line.split(/\s+/);
      props.push([p[1], p[2]]);
    }
  }
  if (!isBinary) throw new Error('Malformed PLY: no binary format line');

  // Row layout
  let rowSize = 0;
  const offset = {};
  const type = {};
  for (const [t, name] of props) {
    const sz = PLY_TYPE_SIZE[t];
    if (!sz) throw new Error(`Unsupported PLY property type '${t}'`);
    offset[name] = rowSize; type[name] = t; rowSize += sz;
  }
  const names = props.map(p => p[1]);
  const body = new DataView(bytes.buffer, bytes.byteOffset + hdrEnd, N * rowSize);

  const allF4 = props.every(p => PLY_TYPE_SIZE[p[0]] === 4 && (p[0] === 'float' || p[0] === 'float32'));
  const P = props.length;
  let fastF32 = null;
  if (allF4) {
    // Bulk view requires 4-byte alignment of the body â€” copy if misaligned
    const start = bytes.byteOffset + hdrEnd;
    fastF32 = (start % 4 === 0)
      ? new Float32Array(bytes.buffer, start, N * P)
      : new Float32Array(bytes.slice(hdrEnd, hdrEnd + N * rowSize).buffer);
  }
  const colIdx = {}; names.forEach((n, j) => colIdx[n] = j);

  function getter(name) {
    if (!(name in offset)) throw new Error(`PLY missing required property '${name}'`);
    if (fastF32) { const j = colIdx[name]; return i => fastF32[i * P + j]; }
    const off = offset[name], t = type[name];
    switch (t) {
      case 'float': case 'float32': return i => body.getFloat32(i * rowSize + off, true);
      case 'double': case 'float64': return i => body.getFloat64(i * rowSize + off, true);
      case 'int': case 'int32': return i => body.getInt32(i * rowSize + off, true);
      case 'uint': case 'uint32': return i => body.getUint32(i * rowSize + off, true);
      case 'short': case 'int16': return i => body.getInt16(i * rowSize + off, true);
      case 'ushort': case 'uint16': return i => body.getUint16(i * rowSize + off, true);
      case 'char': case 'int8': return i => body.getInt8(i * rowSize + off);
      default: return i => body.getUint8(i * rowSize + off);
    }
  }

  const gx = getter('x'), gy = getter('y'), gz = getter('z');
  const gs0 = getter('scale_0'), gs1 = getter('scale_1'), gs2 = getter('scale_2');
  const gr0 = getter('rot_0'), gr1 = getter('rot_1'), gr2 = getter('rot_2'), gr3 = getter('rot_3');
  const gop = getter('opacity');
  const gd0 = getter('f_dc_0'), gd1 = getter('f_dc_1'), gd2 = getter('f_dc_2');

  const restNames = names.filter(n => n.startsWith('f_rest_'))
    .sort((a, b) => parseInt(a.split('_').pop(), 10) - parseInt(b.split('_').pop(), 10));
  const K = restNames.length;
  const restGetters = restNames.map(getter);

  const c = makeCloud(N);
  for (let i = 0; i < N; i++) {
    c.positions[i*3] = gx(i); c.positions[i*3+1] = gy(i); c.positions[i*3+2] = gz(i);
    c.scales[i*3] = gs0(i); c.scales[i*3+1] = gs1(i); c.scales[i*3+2] = gs2(i);
    c.rotations[i*4] = gr0(i); c.rotations[i*4+1] = gr1(i); c.rotations[i*4+2] = gr2(i); c.rotations[i*4+3] = gr3(i);
    c.opacities[i] = gop(i);
    c.shDc[i*3] = gd0(i); c.shDc[i*3+1] = gd1(i); c.shDc[i*3+2] = gd2(i);
  }
  if (K > 0) {
    c.shRest = new Float32Array(N * K); c.shK = K;
    for (let i = 0; i < N; i++)
      for (let k = 0; k < K; k++) c.shRest[i * K + k] = restGetters[k](i);
  }
  // Optional relighting channels
  if (['nx','ny','nz'].every(n => n in offset)) {
    const gnx = getter('nx'), gny = getter('ny'), gnz = getter('nz');
    let any = false;
    const nrm = new Float32Array(N * 3);
    for (let i = 0; i < N; i++) {
      const a = gnx(i), b = gny(i), d = gnz(i);
      nrm[i*3] = a; nrm[i*3+1] = b; nrm[i*3+2] = d;
      if (Math.abs(a) > 1e-9 || Math.abs(b) > 1e-9 || Math.abs(d) > 1e-9) any = true;
    }
    if (any) c.normals = nrm;
  }
  if ('metallic' in offset && 'roughness' in offset) {
    const gm = getter('metallic'), gr = getter('roughness');
    c.mr = new Float32Array(N * 2);
    for (let i = 0; i < N; i++) { c.mr[i*2] = gm(i); c.mr[i*2+1] = gr(i); }
  }
  normalizeRotations(c);
  return c;
}

/* â”€â”€â”€ .ply (INRIA / 3DGS uncompressed) â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
 * Color: f_dc_0…2 = raw SH DC floats. Loaders apply:
 *   display = 0.5 + SH_C0 * f_dc   (SH_C0 ≈ 0.28209479177387814)
 * Do NOT write display-linear RGB into f_dc_* — that washes colors toward gray
 * when GS3D/SuperSplat apply SH_C0 again.
 * Opacity: logit float. Scale: log float. Rotation: wxyz float.
 */

function writePly(c) {
  const N = c.count, K = c.shRest ? c.shK : 0, hasMr = !!c.mr;
  const propNames = ['x','y','z','nx','ny','nz','f_dc_0','f_dc_1','f_dc_2'];
  for (let i = 0; i < K; i++) propNames.push('f_rest_' + i);
  propNames.push('opacity','scale_0','scale_1','scale_2','rot_0','rot_1','rot_2','rot_3');
  if (hasMr) propNames.push('metallic','roughness');

  let hdr = 'ply\nformat binary_little_endian 1.0\n' + `element vertex ${N}\n`;
  for (const n of propNames) hdr += `property float ${n}\n`;
  hdr += 'end_header\n';
  const hdrBytes = new TextEncoder().encode(hdr);

  const P = propNames.length;
  const data = new Float32Array(N * P);
  for (let i = 0; i < N; i++) {
    let j = i * P;
    data[j++] = c.positions[i*3]; data[j++] = c.positions[i*3+1]; data[j++] = c.positions[i*3+2];
    if (c.normals) { data[j++] = c.normals[i*3]; data[j++] = c.normals[i*3+1]; data[j++] = c.normals[i*3+2]; }
    else { data[j++] = 0; data[j++] = 0; data[j++] = 0; }
    data[j++] = c.shDc[i*3]; data[j++] = c.shDc[i*3+1]; data[j++] = c.shDc[i*3+2]; // raw f_dc, not display
    for (let k = 0; k < K; k++) data[j++] = c.shRest[i*K + k];
    data[j++] = c.opacities[i];
    data[j++] = c.scales[i*3]; data[j++] = c.scales[i*3+1]; data[j++] = c.scales[i*3+2];
    data[j++] = c.rotations[i*4]; data[j++] = c.rotations[i*4+1]; data[j++] = c.rotations[i*4+2]; data[j++] = c.rotations[i*4+3];
    if (hasMr) { data[j++] = c.mr[i*2]; data[j++] = c.mr[i*2+1]; }
  }
  const out = new Uint8Array(hdrBytes.length + data.byteLength);
  out.set(hdrBytes, 0);
  out.set(new Uint8Array(data.buffer), hdrBytes.length);
  return out;
}

/* â”€â”€â”€ .splat (antimatter15) â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
 * Color: display RGB u8 = clamp(f_dc * SH_C0 + 0.5). Opacity: sigmoid→u8.
 * Scale: linear float (exp of cloud log). Rotation: wxyz u8. No SH rest.
 */

function readSplat(bytes) {
  const N = Math.floor(bytes.length / SPLAT_ROW_BYTES);
  const dv = new DataView(bytes.buffer, bytes.byteOffset, N * SPLAT_ROW_BYTES);
  const c = makeCloud(N);
  for (let i = 0; i < N; i++) {
    const o = i * SPLAT_ROW_BYTES;
    c.positions[i*3]   = dv.getFloat32(o, true);
    c.positions[i*3+1] = dv.getFloat32(o+4, true);
    c.positions[i*3+2] = dv.getFloat32(o+8, true);
    for (let k = 0; k < 3; k++)
      c.scales[i*3+k] = linearScaleToLog(dv.getFloat32(o+12+4*k, true));
    c.shDc[i*3]   = unpackU8ToShDc(bytes[o+24]);
    c.shDc[i*3+1] = unpackU8ToShDc(bytes[o+25]);
    c.shDc[i*3+2] = unpackU8ToShDc(bytes[o+26]);
    c.opacities[i] = logit(clamp(bytes[o+27] / 255, 1e-6, 1 - 1e-6));
    for (let k = 0; k < 4; k++)
      c.rotations[i*4+k] = clamp((bytes[o+28+k] - 128) / 128, -1, 1);   // wxyz
  }
  normalizeRotations(c);
  return c;
}

function writeSplat(c) {
  const N = c.count;
  const out = new Uint8Array(N * SPLAT_ROW_BYTES);
  const dv = new DataView(out.buffer);
  for (let i = 0; i < N; i++) {
    const o = i * SPLAT_ROW_BYTES;
    dv.setFloat32(o,   c.positions[i*3],   true);
    dv.setFloat32(o+4, c.positions[i*3+1], true);
    dv.setFloat32(o+8, c.positions[i*3+2], true);
    for (let k = 0; k < 3; k++)
      dv.setFloat32(o+12+4*k, logScaleToLinear(c.scales[i*3+k]), true);
    out[o+24] = packShDcToU8(c.shDc[i*3]);
    out[o+25] = packShDcToU8(c.shDc[i*3+1]);
    out[o+26] = packShDcToU8(c.shDc[i*3+2]);
    out[o+27] = clamp(Math.round(sigmoid(c.opacities[i]) * 255), 0, 255);
    for (let k = 0; k < 4; k++)
      out[o+28+k] = clamp(Math.round(c.rotations[i*4+k] * 128 + 128), 0, 255);
  }
  return out;
}

/* â”€â”€â”€ .spz (Niantic / Scaniverse) â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€ */

const SPZ_FLAG_ANTIALIASED = 0x1;

function spzBuildStreams(c, fracBits) {
  const N = c.count;
  const shDeg = cloudShDegree(c);
  const scaleFactor = 1 << fracBits;

  // SuperSplat / splat-transform: SPZ stores PLY/RDF coordinates (no RUB flip).
  const posScaled = new Int32Array(N * 3);
  for (let i = 0; i < N; i++) {
    posScaled[i*3]   = Math.round(c.positions[i*3]   * scaleFactor);
    posScaled[i*3+1] = Math.round(c.positions[i*3+1] * scaleFactor);
    posScaled[i*3+2] = Math.round(c.positions[i*3+2] * scaleFactor);
  }
  const posData = packInt24(posScaled);

  const alpData = new Uint8Array(N);
  for (let i = 0; i < N; i++)
    alpData[i] = clamp(Math.round(sigmoid(c.opacities[i]) * 255), 0, 255);

  // SPZ "colors" are packed SH DC (f_dc), not display RGB — see nianticlabs/spz colorScale=0.15.
  const colData = new Uint8Array(N * 3);
  for (let i = 0; i < N * 3; i++)
    colData[i] = spzShDcToByte(c.shDc[i]);

  const scData = new Uint8Array(N * 3);
  for (let i = 0; i < N * 3; i++)
    scData[i] = clamp(Math.round((c.scales[i] + 10) * 16), 0, 255);

  // v2 rotation: 3×u8 xyz, w reconstructed (positive).
  const rotData = new Uint8Array(N * 3);
  for (let i = 0; i < N; i++) {
    let w = c.rotations[i*4], x = c.rotations[i*4+1], y = c.rotations[i*4+2], z = c.rotations[i*4+3];
    if (w < 0) { w = -w; x = -x; y = -y; z = -z; }
    rotData[i*3]   = clamp(Math.round((x + 1) * 127.5), 0, 255);
    rotData[i*3+1] = clamp(Math.round((y + 1) * 127.5), 0, 255);
    rotData[i*3+2] = clamp(Math.round((z + 1) * 127.5), 0, 255);
  }

  const nRest = SH_REST_COUNT[shDeg] || 0;
  let shData = new Uint8Array(0);
  if (nRest > 0 && c.shRest) {
    shData = new Uint8Array(N * nRest);
    for (let i = 0; i < N; i++)
      for (let k = 0; k < nRest; k++)
        shData[i*nRest + k] = clamp(Math.round(c.shRest[i*c.shK + k] * 128 + 128), 0, 255);
  }
  return { streams: [posData, alpData, colData, scData, rotData, shData], shDeg };
}

/** SPZ v3/v4 smallest-three quat → cloud wxyz (matches splat-transform read-spz). */
function spzUnpackRotationV3(packed, outWxyz, i) {
  // tmp indexed as [x,y,z,w]; largest selector uses that order.
  const tmp = [0, 0, 0, 0];
  let p = packed >>> 0;
  const largest = p >>> 30;
  const cMask = (1 << 9) - 1;
  let sumSq = 0;
  for (let j = 3; j >= 0; --j) {
    if (j !== largest) {
      const mag = p & cMask;
      const neg = (p >>> 9) & 1;
      p >>>= 10;
      let v = (Math.SQRT1_2 * mag) / cMask;
      if (neg) v = -v;
      tmp[j] = v;
      sumSq += v * v;
    }
  }
  tmp[largest] = Math.sqrt(Math.max(0, 1 - sumSq));
  outWxyz[i * 4]     = tmp[3]; // w
  outWxyz[i * 4 + 1] = tmp[0]; // x
  outWxyz[i * 4 + 2] = tmp[1]; // y
  outWxyz[i * 4 + 3] = tmp[2]; // z
}

function spzDecodePayload(payload, N, shDegree, fracBits, version = 2) {
  const scaleF = 1 / (1 << fracBits);
  let off = 0;
  const c = makeCloud(N);
  const rotBytes = version <= 2 ? 3 : 4;

  const flat = unpackInt24(payload.subarray(off, off + N * 9), N * 3); off += N * 9;
  for (let i = 0; i < N; i++) {
    c.positions[i*3]   = flat[i*3]   * scaleF;
    c.positions[i*3+1] = flat[i*3+1] * scaleF;
    c.positions[i*3+2] = flat[i*3+2] * scaleF;
  }
  for (let i = 0; i < N; i++) c.opacities[i] = logit(payload[off + i] / 255); off += N;
  for (let i = 0; i < N * 3; i++) c.shDc[i] = spzByteToShDc(payload[off + i]); off += N * 3;
  for (let i = 0; i < N * 3; i++) c.scales[i] = payload[off + i] / 16 - 10; off += N * 3;

  if (rotBytes === 3) {
    for (let i = 0; i < N; i++) {
      const x = clamp(payload[off + i*3]   / 127.5 - 1, -1, 1);
      const y = clamp(payload[off + i*3+1] / 127.5 - 1, -1, 1);
      const z = clamp(payload[off + i*3+2] / 127.5 - 1, -1, 1);
      const w = Math.sqrt(clamp(1 - (x*x + y*y + z*z), 0, 1));
      c.rotations[i*4] = w; c.rotations[i*4+1] = x;
      c.rotations[i*4+2] = y; c.rotations[i*4+3] = z;
    }
  } else {
    const rdv = new DataView(payload.buffer, payload.byteOffset + off, N * 4);
    for (let i = 0; i < N; i++) spzUnpackRotationV3(rdv.getUint32(i * 4, true), c.rotations, i);
  }
  off += N * rotBytes;

  const nRest = SH_REST_COUNT[shDegree] || 0;
  if (nRest > 0 && off < payload.length) {
    c.shRest = new Float32Array(N * nRest); c.shK = nRest;
    for (let i = 0; i < N * nRest; i++) c.shRest[i] = (payload[off + i] - 128) / 128;
  }
  normalizeRotations(c);
  return c;
}

async function readSpz(bytes) {
  let magic, version, N, shDegree, fracBits, flags = 0, payload;
  const dv = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);

  if (bytes[0] === 0x1f && bytes[1] === 0x8b) {
    // Format B: gzip(16-byte header + payload) — SuperSplat v2/v3
    const inner = await gunzipBytes(bytes);
    const idv = new DataView(inner.buffer, inner.byteOffset, inner.byteLength);
    magic = idv.getUint32(0, true); version = idv.getUint32(4, true); N = idv.getUint32(8, true);
    shDegree = inner[12]; fracBits = inner[13]; flags = inner[14];
    payload = inner.subarray(16);
  } else {
    magic = dv.getUint32(0, true); version = dv.getUint32(4, true); N = dv.getUint32(8, true);
    if (version === 1 || version === 2 || version === 3) {
      shDegree = bytes[12]; fracBits = bytes[13]; flags = bytes[14];
      if (bytes.length > 18 && bytes[16] === 0x1f && bytes[17] === 0x8b) {
        payload = await gunzipBytes(bytes.subarray(16));
      } else if (version === 3) {
        payload = bytes.subarray(16);
      } else {
        payload = await gunzipBytes(bytes.subarray(16));
      }
    } else if (version === 4) {
      if (!globalThis.fzstd) throw new Error('fzstd not available for SPZ v4');
      shDegree = bytes[12]; fracBits = bytes[13]; flags = bytes[14];
      const numStreams = bytes[15];
      const tocOffset = dv.getUint32(16, true);
      const parts = [];
      let streamOff = tocOffset + numStreams * 16;
      let total = 0;
      for (let i = 0; i < numStreams; i++) {
        const compSz = dv.getUint32(tocOffset + i*16, true) + dv.getUint32(tocOffset + i*16 + 4, true) * 4294967296;
        const part = compSz ? globalThis.fzstd.decompress(bytes.subarray(streamOff, streamOff + compSz)) : new Uint8Array(0);
        parts.push(part); total += part.length;
        streamOff += compSz;
      }
      payload = new Uint8Array(total);
      let o = 0;
      for (const p of parts) { payload.set(p, o); o += p.length; }
    } else {
      throw new Error(`SPZ version ${version} not supported (supported: v1–v4)`);
    }
  }
  if (magic !== SPZ_MAGIC) throw new Error('Not an SPZ file (bad magic)');
  const c = spzDecodePayload(payload, N, shDegree, fracBits, version);
  c._importHints = { sogAntialias: !!(flags & SPZ_FLAG_ANTIALIASED) };
  return c;
}

async function writeSpz(c, fracBits = SPZ_DEFAULT_FRAC_BITS) {
  // v2 Format B â€” gzip(16-byte NGSP header + raw payload).
  // Note: gzip level is the browser default (CompressionStream has no level).
  const { streams, shDeg } = spzBuildStreams(c, fracBits);
  let total = 16;
  for (const s of streams) total += s.length;
  const raw = new Uint8Array(total);
  const dv = new DataView(raw.buffer);
  dv.setUint32(0, SPZ_MAGIC, true);
  dv.setUint32(4, 2, true);
  dv.setUint32(8, c.count, true);
  raw[12] = shDeg; raw[13] = fracBits; raw[14] = 0; raw[15] = 0;
  let o = 16;
  for (const s of streams) { raw.set(s, o); o += s.length; }
  return gzipBytes(raw);
}

/* â”€â”€â”€ .compressed.ply (PlayCanvas / SuperSplat) â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
 * Color: chunk min_r/max_r… are display-linear = f_dc * SH_C0 + 0.5
 *        (may be outside [0,1]). packed_color RGB unorm lerps that range;
 *        cloud.shDc stores true f_dc = (display - 0.5) / SH_C0.
 * Opacity: packed_color A = sigmoid(logit) as u8.
 * Scale: chunk min/max are log-scale (same as uncompressed PLY scale_0…2).
 * Axes: same Y-down as 3DGS PLY (no extra flip).
 */

function cplyPackPosSc(vals, s, e, mn, mx, out) {
  const r0 = Math.max(mx[0] - mn[0], 1e-6), r1 = Math.max(mx[1] - mn[1], 1e-6), r2 = Math.max(mx[2] - mn[2], 1e-6);
  for (let i = s; i < e; i++) {
    const x = Math.round(clamp((vals[i*3]   - mn[0]) / r0, 0, 1) * 2047);
    const y = Math.round(clamp((vals[i*3+1] - mn[1]) / r1, 0, 1) * 1023);
    const z = Math.round(clamp((vals[i*3+2] - mn[2]) / r2, 0, 1) * 2047);
    out[i] = ((x << 21) | (y << 11) | z) >>> 0;
  }
}

/**
 * PlayCanvas / SuperSplat compressed-PLY quaternion (2+10+10+10).
 * Selector is the largest component in WXYZ: 0=w, 1=x, 2=y, 3=z.
 * Older GS3D used XYZW (0=x) — that mismatch orients anisotropic splats as needles.
 * Matches playcanvas/engine GSplatCompressedData.unpackRot (Quat.set is x,y,z,w).
 */
function cplyPackRotation(rot, N) {
  const out = new Uint32Array(N);
  for (let i = 0; i < N; i++) {
    const w = rot[i * 4], x = rot[i * 4 + 1], y = rot[i * 4 + 2], z = rot[i * 4 + 3];
    const wxyz = [w, x, y, z];
    let sel = 0, best = Math.abs(wxyz[0]);
    for (let k = 1; k < 4; k++) {
      const a = Math.abs(wxyz[k]);
      if (a > best) { best = a; sel = k; }
    }
    const sign = wxyz[sel] < 0 ? -1 : 1;
    let a, b, c;
    if (sel === 0) { a = x; b = y; c = z; }
    else if (sel === 1) { a = w; b = y; c = z; }
    else if (sel === 2) { a = w; b = x; c = z; }
    else { a = w; b = x; c = y; }
    const e0 = clamp(Math.round(a * sign / SQRT2 * 1023 + 511.5), 0, 1023);
    const e1 = clamp(Math.round(b * sign / SQRT2 * 1023 + 511.5), 0, 1023);
    const e2 = clamp(Math.round(c * sign / SQRT2 * 1023 + 511.5), 0, 1023);
    out[i] = ((sel << 30) | (e0 << 20) | (e1 << 10) | e2) >>> 0;
  }
  return out;
}

function cplyUnpackRotation(packed, N, rotations) {
  for (let i = 0; i < N; i++) {
    const p = packed[i];
    const sel = p >>> 30;
    const a = (((p >>> 20) & 1023) / 1023 - 0.5) * SQRT2;
    const b = (((p >>> 10) & 1023) / 1023 - 0.5) * SQRT2;
    const d = ((p & 1023) / 1023 - 0.5) * SQRT2;
    const m = Math.sqrt(Math.max(0, 1 - (a * a + b * b + d * d)));
    let x, y, z, w;
    switch (sel) {
      case 0: x = a; y = b; z = d; w = m; break;
      case 1: x = m; y = b; z = d; w = a; break;
      case 2: x = b; y = m; z = d; w = a; break;
      default: x = b; y = d; z = m; w = a; break;
    }
    rotations[i * 4] = w;
    rotations[i * 4 + 1] = x;
    rotations[i * 4 + 2] = y;
    rotations[i * 4 + 3] = z;
  }
}

function readCompressedPly(bytes) {
  bytes = ensureBytes(bytes);
  const { lines, hdrEnd } = parsePlyHeader(bytes);
  const elements = {};
  let current = null;
  for (const line of lines) {
    if (line.includes('binary_big_endian')) throw new Error('Big-endian PLY not supported');
    if (line.startsWith('element ')) {
      const p = line.split(/\s+/);
      current = p[1];
      elements[current] = { count: parseInt(p[2], 10), props: [] };
    } else if (line.startsWith('property') && current && !line.includes('list')) {
      const p = line.split(/\s+/);
      elements[current].props.push([p[1], p[2]]);
    }
  }
  if (!elements.chunk || !elements.vertex) throw new Error('Not a PlayCanvas compressed PLY (missing chunk/vertex elements)');

  const nChunks = elements.chunk.count;
  const N = elements.vertex.count;
  const chunkProps = elements.chunk.props.map(p => p[1]);
  const chunkRow = elements.chunk.props.reduce((a, p) => a + PLY_TYPE_SIZE[p[0]], 0);
  const chunkF32 = new Float32Array(bytes.slice(hdrEnd, hdrEnd + nChunks * chunkRow).buffer);
  const CP = chunkProps.length;
  const cIdx = {}; chunkProps.forEach((n, j) => cIdx[n] = j);
  const chunkVal = (ci, name) => chunkF32[ci * CP + cIdx[name]];
  const hasColorExt = ['min_r', 'max_r', 'min_g', 'max_g', 'min_b', 'max_b']
    .every((n) => cIdx[n] != null);

  const vertOff = hdrEnd + nChunks * chunkRow;
  const vertProps = elements.vertex.props.map(p => p[1]);
  const VP = vertProps.length;
  const vIdx = {}; vertProps.forEach((n, j) => vIdx[n] = j);
  const vertU32 = new Uint32Array(bytes.slice(vertOff, vertOff + N * VP * 4).buffer);

  const c = makeCloud(N);
  const packedRot = new Uint32Array(N);
  for (let i = 0; i < N; i++) packedRot[i] = vertU32[i * VP + vIdx.packed_rotation];
  cplyUnpackRotation(packedRot, N, c.rotations);

  const vertsPerChunk = compressedPlyVerticesPerChunk(N, nChunks);
  for (let i = 0; i < N; i++) {
    const ci = Math.min(Math.floor(i / vertsPerChunk), nChunks - 1);
    const mnP = [chunkVal(ci,'min_x'), chunkVal(ci,'min_y'), chunkVal(ci,'min_z')];
    const mxP = [chunkVal(ci,'max_x'), chunkVal(ci,'max_y'), chunkVal(ci,'max_z')];
    const mnS = [chunkVal(ci,'min_scale_x'), chunkVal(ci,'min_scale_y'), chunkVal(ci,'min_scale_z')];
    const mxS = [chunkVal(ci,'max_scale_x'), chunkVal(ci,'max_scale_y'), chunkVal(ci,'max_scale_z')];
    let mnR = 0, mxR = 1, mnG = 0, mxG = 1, mnB = 0, mxB = 1;
    if (hasColorExt) {
      mnR = chunkVal(ci, 'min_r'); mxR = chunkVal(ci, 'max_r');
      mnG = chunkVal(ci, 'min_g'); mxG = chunkVal(ci, 'max_g');
      mnB = chunkVal(ci, 'min_b'); mxB = chunkVal(ci, 'max_b');
    }
    const pp = vertU32[i * VP + vIdx.packed_position];
    const pu = unpack111011(pp);
    c.positions[i*3]   = mnP[0] + pu.x * (mxP[0] - mnP[0]);
    c.positions[i*3+1] = mnP[1] + pu.y * (mxP[1] - mnP[1]);
    c.positions[i*3+2] = mnP[2] + pu.z * (mxP[2] - mnP[2]);
    const ps = vertU32[i * VP + vIdx.packed_scale];
    const su = unpack111011(ps);
    // Chunk min/max are log-scale (scale_0…2), same as uncompressed 3DGS PLY.
    c.scales[i*3]   = mnS[0] + su.x * (mxS[0] - mnS[0]);
    c.scales[i*3+1] = mnS[1] + su.y * (mxS[1] - mnS[1]);
    c.scales[i*3+2] = mnS[2] + su.z * (mxS[2] - mnS[2]);
    const pc = vertU32[i * VP + vIdx.packed_color];
    const nr = ((pc >>> 24) & 0xFF) / 255;
    const ng = ((pc >>> 16) & 0xFF) / 255;
    const nb = ((pc >>>  8) & 0xFF) / 255;
    if (hasColorExt) {
      // PlayCanvas: chunk min/max are display-linear; recover f_dc for the cloud.
      c.shDc[i*3]   = rgbToShDc(mnR + nr * (mxR - mnR));
      c.shDc[i*3+1] = rgbToShDc(mnG + ng * (mxG - mnG));
      c.shDc[i*3+2] = rgbToShDc(mnB + nb * (mxB - mnB));
    } else {
      c.shDc[i*3]   = rgbToShDc(nr);
      c.shDc[i*3+1] = rgbToShDc(ng);
      c.shDc[i*3+2] = rgbToShDc(nb);
    }
    c.opacities[i] = logit((pc & 0xFF) / 255);
  }

  const shEl = elements.sh;
  if (shEl && shEl.count === N && shEl.props.length > 0) {
    const shK = shEl.props.length;
    const shOff = vertOff + N * VP * 4;
    c.shRest = new Float32Array(N * shK);
    c.shK = shK;
    for (let i = 0; i < N; i++) {
      for (let k = 0; k < shK; k++) {
        const b = bytes[shOff + i * shK + k];
        c.shRest[i * shK + k] = cplyShByteToFloat(b);
      }
    }
  }

  normalizeRotations(c);
  return c;
}

function writeCompressedPly(c, chunkSize = CPLY_CHUNK_SIZE) {
  chunkSize = [64, 128, 256, 512].includes(chunkSize | 0) ? chunkSize | 0 : 256;
  const N = c.count;
  const nChunks = Math.ceil(N / chunkSize);
  const shK = c.shRest ? c.shK : 0;

  const order = mortonOrder(c.positions, N);
  const pos = gatherRows(c.positions, order, 3);
  const sc  = gatherRows(c.scales, order, 3);
  const rot = gatherRows(c.rotations, order, 4);
  // PlayCanvas chunk colors are display-linear (f_dc * SH_C0 + 0.5), not raw f_dc.
  const dcA = new Float32Array(N * 3);
  const alpA = new Float32Array(N);
  for (let i = 0; i < N; i++) {
    const s = order[i];
    dcA[i*3]   = shDcToDisplay(c.shDc[s*3]);
    dcA[i*3+1] = shDcToDisplay(c.shDc[s*3+1]);
    dcA[i*3+2] = shDcToDisplay(c.shDc[s*3+2]);
    alpA[i] = sigmoid(c.opacities[s]);
  }

  const chunkFields = ['min_x','min_y','min_z','max_x','max_y','max_z',
    'min_scale_x','min_scale_y','min_scale_z','max_scale_x','max_scale_y','max_scale_z',
    'min_r','min_g','min_b','max_r','max_g','max_b'];
  const chunkFloats = chunkFields.length;
  const chunks = new Float32Array(nChunks * chunkFloats);
  const packedPos = new Uint32Array(N);
  const packedSc  = new Uint32Array(N);

  for (let ci = 0; ci < nChunks; ci++) {
    const s = ci * chunkSize, e = Math.min(s + chunkSize, N);
    const mnP = [Infinity, Infinity, Infinity], mxP = [-Infinity, -Infinity, -Infinity];
    const mnS = [Infinity, Infinity, Infinity], mxS = [-Infinity, -Infinity, -Infinity];
    const mnC = [Infinity, Infinity, Infinity], mxC = [-Infinity, -Infinity, -Infinity];
    for (let i = s; i < e; i++) {
      for (let k = 0; k < 3; k++) {
        const p = pos[i*3+k], q = sc[i*3+k], d = dcA[i*3+k];
        if (p < mnP[k]) mnP[k] = p; if (p > mxP[k]) mxP[k] = p;
        if (q < mnS[k]) mnS[k] = q; if (q > mxS[k]) mxS[k] = q;
        if (d < mnC[k]) mnC[k] = d; if (d > mxC[k]) mxC[k] = d;
      }
    }
    const co = ci * chunkFloats;
    chunks[co] = mnP[0]; chunks[co+1] = mnP[1]; chunks[co+2] = mnP[2];
    chunks[co+3] = mxP[0]; chunks[co+4] = mxP[1]; chunks[co+5] = mxP[2];
    chunks[co+6] = mnS[0]; chunks[co+7] = mnS[1]; chunks[co+8] = mnS[2];
    chunks[co+9] = mxS[0]; chunks[co+10] = mxS[1]; chunks[co+11] = mxS[2];
    chunks[co+12] = mnC[0]; chunks[co+13] = mnC[1]; chunks[co+14] = mnC[2];
    chunks[co+15] = mxC[0]; chunks[co+16] = mxC[1]; chunks[co+17] = mxC[2];
    cplyPackPosSc(pos, s, e, mnP, mxP, packedPos);
    cplyPackPosSc(sc,  s, e, mnS, mxS, packedSc);
  }

  const packedRot = cplyPackRotation(rot, N);
  const packedCol = new Uint32Array(N);
  for (let ci = 0; ci < nChunks; ci++) {
    const s = ci * chunkSize, e = Math.min(s + chunkSize, N);
    const co = ci * chunkFloats;
    const mnC = [chunks[co+12], chunks[co+13], chunks[co+14]];
    const mxC = [chunks[co+15], chunks[co+16], chunks[co+17]];
    for (let i = s; i < e; i++) {
      const packChan = (v, mn, mx) => {
        const r = Math.max(mx - mn, 1e-8);
        return clamp(Math.round(clamp((v - mn) / r, 0, 1) * 255), 0, 255);
      };
      const r = packChan(dcA[i*3],   mnC[0], mxC[0]);
      const g = packChan(dcA[i*3+1], mnC[1], mxC[1]);
      const b = packChan(dcA[i*3+2], mnC[2], mxC[2]);
      const a = clamp(Math.round(alpA[i] * 255), 0, 255);
      packedCol[i] = ((r << 24) | (g << 16) | (b << 8) | a) >>> 0;
    }
  }

  let hdr = 'ply\nformat binary_little_endian 1.0\n' + `element chunk ${nChunks}\n`;
  for (const f of chunkFields) hdr += `property float ${f}\n`;
  hdr += `element vertex ${N}\n`;
  for (const n of ['packed_position','packed_rotation','packed_scale','packed_color'])
    hdr += `property uint ${n}\n`;
  if (shK > 0) {
    hdr += `element sh ${N}\n`;
    for (let k = 0; k < shK; k++) hdr += `property uchar f_rest_${k}\n`;
  }
  hdr += 'end_header\n';
  const hdrBytes = new TextEncoder().encode(hdr);

  const verts = new Uint32Array(N * 4);
  for (let i = 0; i < N; i++) {
    verts[i*4] = packedPos[i]; verts[i*4+1] = packedRot[i];
    verts[i*4+2] = packedSc[i]; verts[i*4+3] = packedCol[i];
  }
  let bodyLen = chunks.byteLength + verts.byteLength;
  let shBytes = null;
  if (shK > 0) {
    shBytes = new Uint8Array(N * shK);
    const shOrd = gatherRows(c.shRest, order, shK);
    for (let i = 0; i < N; i++) {
      for (let k = 0; k < shK; k++)
        shBytes[i * shK + k] = cplyShFloatToByte(shOrd[i * shK + k]);
    }
    bodyLen += shBytes.length;
  }
  const out = new Uint8Array(hdrBytes.length + bodyLen);
  let o = 0;
  out.set(hdrBytes, o); o += hdrBytes.length;
  out.set(new Uint8Array(chunks.buffer), o); o += chunks.byteLength;
  out.set(new Uint8Array(verts.buffer), o); o += verts.byteLength;
  if (shBytes) out.set(shBytes, o);
  return out;
}

/* .ksplat (GS3D SplatBuffer): display RGB u8 via SH_C0; opacity sigmoid→u8;
 * scale linear; rot wxyz f32. Compression level 0. SH degree 0/1/2 (24 floats max —
 * GS3D shaders do not support degree 3). Layout matches SplatBuffer.CompressionLevels[0].
 */

function ksplatBytesPerSplat(shDeg) {
  if (shDeg >= 2) return 140;
  if (shDeg >= 1) return 80;
  return 44;
}

function readKsplat(bytes) {
  const dv = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  const verMajor = bytes[0];
  if (verMajor !== 0) throw new Error(`ksplat version ${verMajor}.${bytes[1]} not supported`);
  const sectionCount = dv.getUint32(8, true);
  const N = dv.getUint32(16, true);
  const compressionLevel = dv.getUint16(20, true);
  if (compressionLevel !== 0)
    throw new Error(`ksplat compression level ${compressionLevel} not supported (only level 0)`);
  const so = KSPLAT_HEADER_BYTES;
  // Section header: sphericalHarmonicsDegree at uint16 offset 20 → byte offset 40
  const shDeg = Math.min(2, dv.getUint16(so + 40, true) || 0);
  const bytesPer = ksplatBytesPerSplat(shDeg);
  const nSh = SH_REST_COUNT[shDeg] || 0;
  const off = KSPLAT_HEADER_BYTES + sectionCount * KSPLAT_SECTION_BYTES;

  const c = makeCloud(N);
  if (nSh > 0) { c.shRest = new Float32Array(N * nSh); c.shK = nSh; }
  for (let i = 0; i < N; i++) {
    const o = off + i * bytesPer;
    c.positions[i*3]   = dv.getFloat32(o, true);
    c.positions[i*3+1] = dv.getFloat32(o+4, true);
    c.positions[i*3+2] = dv.getFloat32(o+8, true);
    for (let k = 0; k < 3; k++)
      c.scales[i*3+k] = linearScaleToLog(dv.getFloat32(o+12+4*k, true));
    // SplatBuffer level-0 stores wxyz (see SplatParser outRotation / getSplatScaleAndRotation).
    for (let k = 0; k < 4; k++)
      c.rotations[i*4+k] = dv.getFloat32(o+24+4*k, true);
    c.shDc[i*3]   = unpackU8ToShDc(bytes[o+40]);
    c.shDc[i*3+1] = unpackU8ToShDc(bytes[o+41]);
    c.shDc[i*3+2] = unpackU8ToShDc(bytes[o+42]);
    c.opacities[i] = logit(clamp(bytes[o+43] / 255, 1e-6, 1 - 1e-6));
    if (nSh > 0) {
      for (let s = 0; s < nSh; s++)
        c.shRest[i * nSh + s] = dv.getFloat32(o + 44 + s * 4, true);
    }
  }
  normalizeRotations(c);
  return c;
}

function writeKsplat(c) {
  const N = c.count;
  // GS3D viewport/shader max is degree 2 — match editor sphericalHarmonicsDegree: 2.
  const shDeg = Math.min(2, cloudShDegree(c));
  const bytesPer = ksplatBytesPerSplat(shDeg);
  const nSh = SH_REST_COUNT[shDeg] || 0;
  const out = new Uint8Array(KSPLAT_HEADER_BYTES + KSPLAT_SECTION_BYTES + N * bytesPer);
  const dv = new DataView(out.buffer);

  let cx = 0, cy = 0, cz = 0;
  for (let i = 0; i < N; i++) { cx += c.positions[i*3]; cy += c.positions[i*3+1]; cz += c.positions[i*3+2]; }
  cx /= Math.max(N, 1); cy /= Math.max(N, 1); cz /= Math.max(N, 1);

  let minSh = 0, maxSh = 0;
  if (nSh > 0 && c.shRest) {
    minSh = Infinity; maxSh = -Infinity;
    for (let i = 0; i < N; i++) {
      for (let s = 0; s < nSh; s++) {
        const v = c.shRest[i * c.shK + s];
        if (v < minSh) minSh = v;
        if (v > maxSh) maxSh = v;
      }
    }
    if (!Number.isFinite(minSh)) { minSh = -1; maxSh = 1; }
  }

  out[0] = 0; out[1] = 1;                       // version 0.1
  dv.setUint32(4, 1, true);                     // maxSectionCount
  dv.setUint32(8, 1, true);                     // sectionCount
  dv.setUint32(12, N, true);                    // maxSplatCount
  dv.setUint32(16, N, true);                    // splatCount
  dv.setUint16(20, 0, true);                    // compressionLevel
  dv.setFloat32(24, cx, true); dv.setFloat32(28, cy, true); dv.setFloat32(32, cz, true);
  dv.setFloat32(36, minSh, true); dv.setFloat32(40, maxSh, true);

  const so = KSPLAT_HEADER_BYTES;
  dv.setUint32(so, N, true);                    // splatCount
  dv.setUint32(so+4, N, true);                  // maxSplatCount
  dv.setUint32(so+24, 1, true);                 // compressionScaleRange
  dv.setUint32(so+28, N * bytesPer, true);      // storageSizeBytes (informational)
  dv.setUint16(so+40, shDeg, true);             // sphericalHarmonicsDegree

  const base = KSPLAT_HEADER_BYTES + KSPLAT_SECTION_BYTES;
  for (let i = 0; i < N; i++) {
    const o = base + i * bytesPer;
    dv.setFloat32(o,   c.positions[i*3], true);
    dv.setFloat32(o+4, c.positions[i*3+1], true);
    dv.setFloat32(o+8, c.positions[i*3+2], true);
    for (let k = 0; k < 3; k++) dv.setFloat32(o+12+4*k, logScaleToLinear(c.scales[i*3+k]), true);
    for (let k = 0; k < 4; k++) dv.setFloat32(o+24+4*k, c.rotations[i*4+k], true);
    out[o+40] = packShDcToU8(c.shDc[i*3]);
    out[o+41] = packShDcToU8(c.shDc[i*3+1]);
    out[o+42] = packShDcToU8(c.shDc[i*3+2]);
    out[o+43] = clamp(Math.round(sigmoid(c.opacities[i]) * 255), 0, 255);
    if (nSh > 0 && c.shRest) {
      for (let s = 0; s < nSh; s++)
        dv.setFloat32(o + 44 + s * 4, c.shRest[i * c.shK + s] || 0, true);
    }
  }
  return out;
}

/* â”€â”€â”€ PNG encoder (exact, for SOG data textures) â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€ */

const CRC_TABLE = (() => {
  const t = new Uint32Array(256);
  for (let n = 0; n < 256; n++) {
    let cc = n;
    for (let k = 0; k < 8; k++) cc = (cc & 1) ? 0xEDB88320 ^ (cc >>> 1) : cc >>> 1;
    t[n] = cc >>> 0;
  }
  return t;
})();
function crc32(u8) {
  let cc = 0xFFFFFFFF;
  for (let i = 0; i < u8.length; i++) cc = CRC_TABLE[(cc ^ u8[i]) & 0xFF] ^ (cc >>> 8);
  return (cc ^ 0xFFFFFFFF) >>> 0;
}
function pngChunk(typeStr, data) {
  const type = new TextEncoder().encode(typeStr);
  const out = new Uint8Array(8 + data.length + 4);
  const dv = new DataView(out.buffer);
  dv.setUint32(0, data.length, false);
  out.set(type, 4);
  out.set(data, 8);
  const crcBuf = new Uint8Array(4 + data.length);
  crcBuf.set(type, 0); crcBuf.set(data, 4);
  dv.setUint32(8 + data.length, crc32(crcBuf), false);
  return out;
}
async function encodePngRgba(rgba /* Uint8Array w*h*4 */, w, h) {
  const ihdr = new Uint8Array(13);
  const idv = new DataView(ihdr.buffer);
  idv.setUint32(0, w, false); idv.setUint32(4, h, false);
  ihdr[8] = 8;   // bit depth
  ihdr[9] = 6;   // color type RGBA
  // scanlines with filter byte 0
  const raw = new Uint8Array(h * (1 + w * 4));
  for (let y = 0; y < h; y++) {
    raw[y * (1 + w*4)] = 0;
    raw.set(rgba.subarray(y * w * 4, (y + 1) * w * 4), y * (1 + w*4) + 1);
  }
  const idat = await zlibBytes(raw);
  const sig = new Uint8Array([137, 80, 78, 71, 13, 10, 26, 10]);
  const c1 = pngChunk('IHDR', ihdr), c2 = pngChunk('IDAT', idat), c3 = pngChunk('IEND', new Uint8Array(0));
  const out = new Uint8Array(sig.length + c1.length + c2.length + c3.length);
  let o = 0;
  for (const part of [sig, c1, c2, c3]) { out.set(part, o); o += part.length; }
  return out;
}

/* Decode any browser-supported image bytes â†’ flat RGBA (no premultiply) */
async function decodeImageRgba(bytes, mime) {
  const blob = new Blob([bytes], { type: mime || 'image/webp' });
  const bmp = await createImageBitmap(blob, { colorSpaceConversion: 'none', premultiplyAlpha: 'none' });
  const cv = new OffscreenCanvas(bmp.width, bmp.height);
  const ctx = cv.getContext('2d', { willReadFrequently: true });
  ctx.drawImage(bmp, 0, 0);
  return { data: ctx.getImageData(0, 0, bmp.width, bmp.height).data, width: bmp.width, height: bmp.height };
}

/* .sog (PlayCanvas): sh0 codebook = f_dc; scales codebook = log; opacity A u8. */

function sogTextureSize(N) {
  const w = Math.max(Math.ceil(Math.sqrt(Math.max(N, 1)) / 4) * 4, 4);
  const h = Math.max(Math.ceil(N / w / 4) * 4, 4);
  return [w, h];
}
const logT = v => Math.sign(v) * Math.log1p(Math.abs(v));
const invLogT = v => Math.sign(v) * Math.expm1(Math.abs(v));

const SOG_QUAT_IDX = [[1,2,3],[0,2,3],[0,1,3],[0,1,2]];
/** AC SH coeffs per band (matches @playcanvas/splat-transform SOG v2). */
const SOG_SH_BAND_COEFFS = [0, 3, 8, 15];

/* Minimal read-only zip (store + deflate) exposing the JSZip subset readSog
 * uses — lets exported AR/HTML pages read .sog without bundling JSZip. */
function openMiniZip(u8) {
  const dv = new DataView(u8.buffer, u8.byteOffset, u8.byteLength);
  let eocd = -1;
  for (let i = u8.length - 22; i >= Math.max(0, u8.length - 65557); i--) {
    if (dv.getUint32(i, true) === 0x06054b50) { eocd = i; break; }
  }
  if (eocd < 0) throw new Error('Not a zip (missing end of central directory)');
  const total = dv.getUint16(eocd + 10, true);
  let p = dv.getUint32(eocd + 16, true);
  const entries = new Map();
  const td = new TextDecoder();
  for (let n = 0; n < total; n++) {
    if (dv.getUint32(p, true) !== 0x02014b50) break;
    const method = dv.getUint16(p + 10, true);
    const csize = dv.getUint32(p + 20, true);
    const nameLen = dv.getUint16(p + 28, true);
    const extraLen = dv.getUint16(p + 30, true);
    const commentLen = dv.getUint16(p + 32, true);
    const localOff = dv.getUint32(p + 42, true);
    const name = td.decode(u8.subarray(p + 46, p + 46 + nameLen));
    entries.set(name, { method, csize, localOff });
    p += 46 + nameLen + extraLen + commentLen;
  }
  async function inflate(e) {
    const lo = e.localOff;
    const start = lo + 30 + dv.getUint16(lo + 26, true) + dv.getUint16(lo + 28, true);
    const raw = u8.subarray(start, start + e.csize);
    if (e.method === 0) return raw.slice();
    if (e.method !== 8) throw new Error(`Unsupported zip compression method ${e.method}`);
    const ds = new DecompressionStream('deflate-raw');
    const ab = await new Response(new Blob([raw]).stream().pipeThrough(ds)).arrayBuffer();
    return new Uint8Array(ab);
  }
  return {
    file(name) {
      const e = entries.get(name);
      if (!e) return null;
      return {
        async async(type) {
          const out = await inflate(e);
          return type === 'string' ? td.decode(out) : out;
        },
      };
    },
  };
}

async function readSog(bytes) {
  const zip = globalThis.JSZip
    ? await new globalThis.JSZip().loadAsync(bytes)
    : openMiniZip(ensureBytes(bytes));
  const metaFile = zip.file('meta.json');
  if (!metaFile) throw new Error('Not a SOG bundle (missing meta.json)');
  const meta = JSON.parse(await metaFile.async('string'));
  if (meta.version !== 2)
    throw new Error(`Unsupported SOG version ${meta.version} â€” only version 2 is supported`);
  // Older tools wrote codebook[0] = null â€” patch like the PlayCanvas engine
  for (const k of ['scales', 'sh0']) {
    const cb = meta[k] && meta[k].codebook;
    if (cb && cb[0] === null) cb[0] = cb[1] + (cb[1] - cb[255]) / 255;
  }
  const N = meta.count;

  async function loadRgba(name) {
    const f = zip.file(name);
    if (!f) throw new Error(`SOG bundle missing ${name}`);
    return decodeImageRgba(await f.async('uint8array'));
  }
  const meansLo = await loadRgba(meta.means.files[0]);
  const meansHi = await loadRgba(meta.means.files[1]);
  const quatsDec = await loadRgba(meta.quats.files[0]);
  const scalesDec = await loadRgba(meta.scales.files[0]);
  const sh0Dec = await loadRgba(meta.sh0.files[0]);
  const ML = meansLo.data, MU = meansHi.data;
  const QT = quatsDec.data, SC = scalesDec.data, S0 = sh0Dec.data;

  const mins = meta.means.mins, maxs = meta.means.maxs;
  const scCB = meta.scales.codebook;
  const s0CB = meta.sh0.codebook;

  const c = makeCloud(N);
  for (let i = 0; i < N; i++) {
    const p = i * 4;
    const qx = ML[p]   | (MU[p]   << 8);
    const qy = ML[p+1] | (MU[p+1] << 8);
    const qz = ML[p+2] | (MU[p+2] << 8);
    c.positions[i*3]   = invLogT(mins[0] + (maxs[0] - mins[0]) * qx / 65535);
    c.positions[i*3+1] = invLogT(mins[1] + (maxs[1] - mins[1]) * qy / 65535);
    c.positions[i*3+2] = invLogT(mins[2] + (maxs[2] - mins[2]) * qz / 65535);

    c.scales[i*3]   = scCB[SC[p]];
    c.scales[i*3+1] = scCB[SC[p+1]];
    c.scales[i*3+2] = scCB[SC[p+2]];

    const tag = QT[p + 3];
    if (tag >= 252 && tag <= 255) {
      const mode = tag - 252;
      const a = (QT[p]   / 255 - 0.5) * SQRT2;
      const b = (QT[p+1] / 255 - 0.5) * SQRT2;
      const d = (QT[p+2] / 255 - 0.5) * SQRT2;
      const lg = Math.sqrt(Math.max(0, 1 - (a*a + b*b + d*d)));
      const wxyz = [0, 0, 0, 0];
      wxyz[mode] = lg;
      const oth = SOG_QUAT_IDX[mode];
      wxyz[oth[0]] = a; wxyz[oth[1]] = b; wxyz[oth[2]] = d;
      c.rotations[i*4] = wxyz[0]; c.rotations[i*4+1] = wxyz[1];
      c.rotations[i*4+2] = wxyz[2]; c.rotations[i*4+3] = wxyz[3];
    } else {
      c.rotations[i*4] = 1; c.rotations[i*4+1] = 0;
      c.rotations[i*4+2] = 0; c.rotations[i*4+3] = 0;
    }

    c.shDc[i*3]   = s0CB[S0[p]];
    c.shDc[i*3+1] = s0CB[S0[p+1]];
    c.shDc[i*3+2] = s0CB[S0[p+2]];
    c.opacities[i] = logit(clamp(S0[p+3] / 255, 1e-6, 1 - 1e-6));
  }
  normalizeRotations(c);

  // Optional higher-order SH (shN palette) — centroids.webp then labels.webp
  if (meta.shN && meta.shN.files && meta.shN.files.length >= 2) {
    const bands = Math.min(3, meta.shN.bands | 0) || 1;
    const shCoeffs = SOG_SH_BAND_COEFFS[bands] || 0;
    const nComp = shCoeffs * 3;
    if (shCoeffs > 0) {
      const shCB = meta.shN.codebook || [];
      if (shCB[0] === null) shCB[0] = shCB[1] + (shCB[1] - shCB[255]) / 255;
      const cenDec = await loadRgba(meta.shN.files[0]);
      const labDec = await loadRgba(meta.shN.files[1]);
      const CENT = cenDec.data, LAB = labDec.data;
      const cW = cenDec.width, cH = cenDec.height;
      const paletteCount = meta.shN.count | 0;
      c.shRest = new Float32Array(N * nComp);
      c.shK = nComp;
      for (let i = 0; i < N; i++) {
        const p = i * 4;
        const label = LAB[p] | (LAB[p + 1] << 8);
        const base = i * nComp;
        if (label < paletteCount) {
          const cy = Math.floor(label / 64);
          const cxBase = (label % 64) * shCoeffs;
          const cyOk = cy < cH;
          for (let j = 0; j < shCoeffs; j++) {
            const cx = cxBase + j;
            const ok = cyOk && cx < cW;
            const idx = (cy * cW + cx) * 4;
            const lr = ok ? CENT[idx] : 0;
            const lg = ok ? CENT[idx + 1] : 0;
            const lb = ok ? CENT[idx + 2] : 0;
            // Channel-major like PLY f_rest_*: R coeffs, then G, then B.
            c.shRest[base + j]                = shCB[lr] ?? 0;
            c.shRest[base + shCoeffs + j]     = shCB[lg] ?? 0;
            c.shRest[base + 2 * shCoeffs + j] = shCB[lb] ?? 0;
          }
        }
      }
    }
  }
  c._importHints = { sogAntialias: !!meta.antialias };
  return c;
}

/** Splat indices sorted by 30-bit Morton code of position (spatial locality). */
function sogMortonOrder(c) {
  const N = c.count, P = c.positions;
  const mn = [Infinity, Infinity, Infinity], mx = [-Infinity, -Infinity, -Infinity];
  for (let i = 0; i < N; i++) {
    for (let k = 0; k < 3; k++) {
      const v = P[i * 3 + k];
      if (v < mn[k]) mn[k] = v;
      if (v > mx[k]) mx[k] = v;
    }
  }
  const part = (v) => {
    v &= 0x3ff;
    v = (v | (v << 16)) & 0x030000ff;
    v = (v | (v << 8)) & 0x0300f00f;
    v = (v | (v << 4)) & 0x030c30c3;
    v = (v | (v << 2)) & 0x09249249;
    return v;
  };
  const q = (i, k) => {
    const span = mx[k] - mn[k];
    const t = span > 0 && Number.isFinite(span) ? (P[i * 3 + k] - mn[k]) / span : 0;
    return clamp(Math.floor(t * 1023), 0, 1023);
  };
  const code = new Uint32Array(N);
  for (let i = 0; i < N; i++)
    code[i] = (part(q(i, 0)) | (part(q(i, 1)) << 1) | (part(q(i, 2)) << 2)) >>> 0;
  const order = new Uint32Array(N);
  for (let i = 0; i < N; i++) order[i] = i;
  order.sort((a, b) => code[a] - code[b]);
  return order;
}

async function writeSog(c, zipLevel = 5) {
  if (!globalThis.JSZip) throw new Error('JSZip not available for SOG support');
  zipLevel = clamp(zipLevel | 0, 1, 9);
  const N = c.count;
  const [w, h] = sogTextureSize(N);
  const total = w * h;

  const mk = () => {
    const a = new Uint8Array(total * 4);
    for (let i = N; i < total; i++) a[i*4+3] = 255;   // opaque padding
    return a;
  };
  const ml = mk(), mu = mk(), qt = mk(), sc = mk(), s0 = mk();

  // Positions: log-transform â†’ 16-bit
  let lpMin = [Infinity, Infinity, Infinity], lpMax = [-Infinity, -Infinity, -Infinity];
  const logPos = new Float32Array(N * 3);
  for (let i = 0; i < N * 3; i++) logPos[i] = logT(c.positions[i]);
  for (let i = 0; i < N; i++)
    for (let k = 0; k < 3; k++) {
      const v = logPos[i*3+k];
      if (v < lpMin[k]) lpMin[k] = v;
      if (v > lpMax[k]) lpMax[k] = v;
    }
  const lpRng = lpMin.map((mn, k) => Math.max(lpMax[k] - mn, 1e-6));
  for (let i = 0; i < N; i++) {
    for (let k = 0; k < 3; k++) {
      const e = clamp(Math.round(65535 * (logPos[i*3+k] - lpMin[k]) / lpRng[k]), 0, 65535);
      ml[i*4+k] = e & 0xFF;
      mu[i*4+k] = e >> 8;
    }
    ml[i*4+3] = 255; mu[i*4+3] = 255;
  }

  // Rotations: smallest-3
  for (let i = 0; i < N; i++) {
    const r = [c.rotations[i*4], c.rotations[i*4+1], c.rotations[i*4+2], c.rotations[i*4+3]];  // wxyz
    let mode = 0, best = Math.abs(r[0]);
    for (let k = 1; k < 4; k++) { const a = Math.abs(r[k]); if (a > best) { best = a; mode = k; } }
    let sign = r[mode] < 0 ? -1 : 1;
    if (r[mode] === 0) sign = 1;
    const oth = SOG_QUAT_IDX[mode];
    for (let k = 0; k < 3; k++) {
      const comp = r[oth[k]] * sign * SQRT2;
      qt[i*4+k] = clamp(Math.round(255 * (comp * 0.5 + 0.5)), 0, 255);
    }
    qt[i*4+3] = 252 + mode;
  }

  // Codebooks (uniform â€” nearest index = linear quantize)
  function buildCodebook(arr) {
    let mn = Infinity, mx = -Infinity;
    for (let i = 0; i < arr.length; i++) { const v = arr[i]; if (v < mn) mn = v; if (v > mx) mx = v; }
    if (mx === mn) mx = mn + 1;
    const cb = new Array(256);
    for (let i = 0; i < 256; i++) cb[i] = mn + (mx - mn) * i / 255;
    return { cb, mn, step: (mx - mn) / 255 };
  }
  const scCB = buildCodebook(c.scales);
  for (let i = 0; i < N; i++) {
    for (let k = 0; k < 3; k++)
      sc[i*4+k] = clamp(Math.round((c.scales[i*3+k] - scCB.mn) / scCB.step), 0, 255);
    sc[i*4+3] = 255;
  }
  const s0CB = buildCodebook(c.shDc);
  for (let i = 0; i < N; i++) {
    for (let k = 0; k < 3; k++)
      s0[i*4+k] = clamp(Math.round((c.shDc[i*3+k] - s0CB.mn) / s0CB.step), 0, 255);
    s0[i*4+3] = clamp(Math.round(sigmoid(c.opacities[i]) * 255), 0, 255);
  }

  const meta = {
    version: 2,
    asset: { generator: 'gaussian-splat-converter' },
    count: N,
    means:  { mins: lpMin, maxs: lpMax, files: ['means_l.webp', 'means_u.webp'] },
    scales: { codebook: scCB.cb, files: ['scales.webp'] },
    quats:  { files: ['quats.webp'] },
    sh0:    { codebook: s0CB.cb, files: ['sh0.webp'] },
  };

  // Lossless PNG bytes under the canonical .webp names â€” see header comment.
  const zip = new globalThis.JSZip();
  zip.file('meta.json', JSON.stringify(meta));
  zip.file('means_l.webp', await encodePngRgba(ml, w, h));
  zip.file('means_u.webp', await encodePngRgba(mu, w, h));
  zip.file('quats.webp',   await encodePngRgba(qt, w, h));
  zip.file('scales.webp',  await encodePngRgba(sc, w, h));
  zip.file('sh0.webp',     await encodePngRgba(s0, w, h));

  // Higher-order SH via palette (≤65536 centroids, 16-bit labels). Not full k-means:
  // splats are grouped in Morton (spatial) order and each group stores its mean SH.
  // Centroid texture follows the PlayCanvas layout readSog expects: 64 centroids per
  // row, one pixel per coefficient holding (R, G, B) from channel-major f_rest.
  const bands = Math.min(2, cloudShDegree(c));
  if (bands >= 1 && c.shRest && c.shK >= SH_REST_COUNT[bands]) {
    const nComp = SH_REST_COUNT[bands];
    const nCoeff = nComp / 3;
    const srcCoeff = (c.shK / 3) | 0;
    const maxCent = 65536;
    const stride = Math.max(1, Math.ceil(N / maxCent));
    const nCent = Math.ceil(N / stride);
    const order = sogMortonOrder(c);
    const lab = new Uint32Array(N);
    const shFlat = new Float32Array(nCent * nComp);
    const cnt = new Uint32Array(nCent);
    for (let r = 0; r < N; r++) {
      const i = order[r];
      const g = Math.min(Math.floor(r / stride), nCent - 1);
      lab[i] = g;
      cnt[g]++;
      const sb = i * c.shK;
      for (let k = 0; k < 3; k++)
        for (let ci = 0; ci < nCoeff; ci++)
          shFlat[g * nComp + k * nCoeff + ci] += c.shRest[sb + k * srcCoeff + ci] || 0;
    }
    for (let g = 0; g < nCent; g++) {
      const inv = cnt[g] ? 1 / cnt[g] : 0;
      for (let s = 0; s < nComp; s++) shFlat[g * nComp + s] *= inv;
    }
    const shNCB = buildCodebook(shFlat);
    const cw = 64 * nCoeff;
    const ch = Math.ceil(nCent / 64);
    const cent = new Uint8Array(cw * ch * 4);
    for (let i = 0; i < cw * ch; i++) cent[i * 4 + 3] = 255;
    for (let j = 0; j < nCent; j++) {
      const row = Math.floor(j / 64);
      const colBase = (j % 64) * nCoeff;
      for (let ci = 0; ci < nCoeff; ci++) {
        const o = (row * cw + colBase + ci) * 4;
        for (let k = 0; k < 3; k++) {
          const v = shFlat[j * nComp + k * nCoeff + ci];
          cent[o + k] = clamp(Math.round((v - shNCB.mn) / shNCB.step), 0, 255);
        }
      }
    }
    const labels = mk();
    for (let i = 0; i < N; i++) {
      const lab_i = lab[i];
      labels[i * 4] = lab_i & 0xff;
      labels[i * 4 + 1] = (lab_i >> 8) & 0xff;
      labels[i * 4 + 2] = 0;
      labels[i * 4 + 3] = 255;
    }
    meta.shN = {
      count: nCent,
      bands,
      codebook: shNCB.cb,
      files: ['shN_centroids.webp', 'shN_labels.webp'],
    };
    zip.file('meta.json', JSON.stringify(meta));
    zip.file('shN_centroids.webp', await encodePngRgba(cent, cw, ch));
    zip.file('shN_labels.webp', await encodePngRgba(labels, w, h));
  }

  return zip.generateAsync({
    type: 'uint8array', compression: 'DEFLATE', compressionOptions: { level: zipLevel },
  });
}

/* â”€â”€â”€ .glb (KHR_gaussian_splatting) â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
 * Color: SH_DEGREE_0_COEF_0 = f_dc VEC3. Opacity: linear [0,1]. Scale: linear.
 * Axes: glTF Y-up on disk ↔ 180° X to/from cloud Y-down. Mesh GLB is separate.
 */

const GLB_MAGIC = 0x46546C67, GLB_JSON = 0x4E4F534A, GLB_BIN = 0x004E4942;
const GLTF_NCOMP = { SCALAR: 1, VEC2: 2, VEC3: 3, VEC4: 4 };
const KHR_SH_COL_OFFSET = { 1: 0, 2: 9, 3: 24 };
const KHR_SH_NCOEF = { 1: 3, 2: 5, 3: 7 };

function glbParse(bytes) {
  const dv = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  if (bytes.length < 12 || dv.getUint32(0, true) !== GLB_MAGIC)
    throw new Error('Not a GLB file. Tip: plain .gltf text files are not supported â€” convert to .glb first.');
  if (dv.getUint32(4, true) !== 2) throw new Error('Only GLB version 2 is supported');
  let jsonBytes = null, binBytes = new Uint8Array(0);
  let off = 12;
  while (off + 8 <= bytes.length) {
    const len = dv.getUint32(off, true), type = dv.getUint32(off + 4, true);
    off += 8;
    const chunk = bytes.subarray(off, off + len);
    off += len;
    if (type === GLB_JSON) jsonBytes = chunk;
    else if (type === GLB_BIN) binBytes = chunk;
  }
  if (!jsonBytes) throw new Error('GLB missing JSON chunk');
  return { gltf: JSON.parse(new TextDecoder('utf-8').decode(jsonBytes)), bin: binBytes };
}

function gltfGetArray(gltf, bin, accIdx) {
  const acc = gltf.accessors[accIdx];
  const bv = gltf.bufferViews[acc.bufferView];
  const count = acc.count;
  const nComp = GLTF_NCOMP[acc.type] || 1;
  const ctype = acc.componentType;
  const sizes = { 5120: 1, 5121: 1, 5122: 2, 5123: 2, 5125: 4, 5126: 4 };
  const csz = sizes[ctype];
  if (!csz) throw new Error(`Unsupported glTF componentType ${ctype}`);
  const elemBytes = csz * nComp;
  const stride = bv.byteStride || elemBytes;
  const base = (bv.byteOffset || 0) + (acc.byteOffset || 0);
  const dv = new DataView(bin.buffer, bin.byteOffset, bin.byteLength);

  const out = new Float32Array(count * nComp);
  const read = {
    5120: o => dv.getInt8(o), 5121: o => dv.getUint8(o),
    5122: o => dv.getInt16(o, true), 5123: o => dv.getUint16(o, true),
    5125: o => dv.getUint32(o, true), 5126: o => dv.getFloat32(o, true),
  }[ctype];
  for (let i = 0; i < count; i++) {
    const ro = base + i * stride;
    for (let k = 0; k < nComp; k++) out[i * nComp + k] = read(ro + k * csz);
  }
  if (acc.normalized) {
    const div = { 5120: 127, 5121: 255, 5122: 32767, 5123: 65535 }[ctype];
    if (div) {
      const signed = ctype === 5120 || ctype === 5122;
      for (let i = 0; i < out.length; i++)
        out[i] = signed ? clamp(out[i] / div, -1, 1) : out[i] / div;
    }
  }
  return out;
}

function readGlb(bytes) {
  const { gltf, bin } = glbParse(bytes);
  let prim = null;
  for (const mesh of gltf.meshes || []) {
    for (const p of mesh.primitives || []) {
      if ((p.mode === undefined ? 4 : p.mode) === 0 && p.extensions && p.extensions.KHR_gaussian_splatting) {
        prim = p; break;
      }
    }
    if (prim) break;
  }
  if (!prim)
    throw new Error('No KHR_gaussian_splatting POINTS primitive found in this GLB.');

  const attrs = prim.attributes;
  const ga = key => {
    if (!(key in attrs)) throw new Error(`Required KHR_gaussian_splatting attribute '${key}' not found`);
    return gltfGetArray(gltf, bin, attrs[key]);
  };
  const positions = ga('POSITION');
  const N = gltf.accessors[attrs.POSITION].count;
  const rotXyzw = ga('KHR_gaussian_splatting:ROTATION');
  const scaleLin = ga('KHR_gaussian_splatting:SCALE');
  const opLin = ga('KHR_gaussian_splatting:OPACITY');
  const shDc = ga('KHR_gaussian_splatting:SH_DEGREE_0_COEF_0');

  const c = makeCloud(N);
  for (let i = 0; i < N; i++) {
    // glTF Y-up on disk → cloud Y-down via 180° X (same half-turn as SPZ).
    const [px, py, pz] = apply180XPos(positions[i*3], positions[i*3+1], positions[i*3+2]);
    c.positions[i*3] = px; c.positions[i*3+1] = py; c.positions[i*3+2] = pz;
    // KHR stores xyzw; cloud stores wxyz. Apply 180° X after xyzw→wxyz.
    const [rw, rx, ry, rz] = apply180XQuatWxyz(
      rotXyzw[i*4+3], rotXyzw[i*4], rotXyzw[i*4+1], rotXyzw[i*4+2],
    );
    c.rotations[i*4] = rw; c.rotations[i*4+1] = rx;
    c.rotations[i*4+2] = ry; c.rotations[i*4+3] = rz;
    for (let k = 0; k < 3; k++)
      c.scales[i*3+k] = linearScaleToLog(scaleLin[i*3+k]);
    c.opacities[i] = logit(opLin[i]);
    c.shDc[i*3] = shDc[i*3]; c.shDc[i*3+1] = shDc[i*3+1]; c.shDc[i*3+2] = shDc[i*3+2];
  }

  // Optional higher SH degrees â€” must be fully present per degree
  const blocks = [];
  let totalK = 0;
  for (const d of [1, 2, 3]) {
    const nCoeff = KHR_SH_NCOEF[d];
    const degArrs = [];
    for (let ci = 0; ci < nCoeff; ci++) {
      const key = `KHR_gaussian_splatting:SH_DEGREE_${d}_COEF_${ci}`;
      if (!(key in attrs)) break;
      degArrs.push(gltfGetArray(gltf, bin, attrs[key]));
    }
    if (degArrs.length < nCoeff) break;
    blocks.push(degArrs); totalK += nCoeff * 3;
  }
  if (totalK > 0) {
    c.shRest = new Float32Array(N * totalK); c.shK = totalK;
    let colBase = 0;
    for (const degArrs of blocks) {
      for (let ci = 0; ci < degArrs.length; ci++) {
        const arr = degArrs[ci];
        for (let i = 0; i < N; i++)
          for (let k = 0; k < 3; k++)
            c.shRest[i * totalK + colBase + 3*ci + k] = arr[i*3+k];
      }
      colBase += degArrs.length * 3;
    }
  }
  normalizeRotations(c);
  return c;
}

function writeGlb(c) {
  const N = c.count;
  const bufParts = [];
  const bvList = [];
  const accList = [];
  const primAttrs = {};
  let bufLen = 0;

  function add(name, arr /* Float32Array */, gltfType) {
    const nComp = GLTF_NCOMP[gltfType];
    const data = new Uint8Array(arr.buffer.slice(arr.byteOffset, arr.byteOffset + arr.byteLength));
    bvList.push({ buffer: 0, byteOffset: bufLen, byteLength: data.length });
    bufParts.push(data); bufLen += data.length;

    const mn = new Array(nComp).fill(Infinity), mx = new Array(nComp).fill(-Infinity);
    for (let i = 0; i < N; i++)
      for (let k = 0; k < nComp; k++) {
        const v = arr[i * nComp + k];
        if (v < mn[k]) mn[k] = v; if (v > mx[k]) mx[k] = v;
      }
    primAttrs[name] = accList.length;
    accList.push({ bufferView: bvList.length - 1, componentType: 5126, count: N, type: gltfType, min: mn, max: mx });
  }

  const pos = new Float32Array(N * 3);
  for (let i = 0; i < N; i++) {
    const [px, py, pz] = apply180XPos(c.positions[i*3], c.positions[i*3+1], c.positions[i*3+2]);
    pos[i*3] = px; pos[i*3+1] = py; pos[i*3+2] = pz;
  }
  add('POSITION', pos, 'VEC3');

  const rot = new Float32Array(N * 4);
  for (let i = 0; i < N; i++) {
    // Cloud wxyz → 180° X → KHR xyzw
    const [rw, rx, ry, rz] = apply180XQuatWxyz(
      c.rotations[i*4], c.rotations[i*4+1], c.rotations[i*4+2], c.rotations[i*4+3],
    );
    rot[i*4] = rx; rot[i*4+1] = ry; rot[i*4+2] = rz; rot[i*4+3] = rw;
  }
  add('KHR_gaussian_splatting:ROTATION', rot, 'VEC4');

  const scl = new Float32Array(N * 3);
  for (let i = 0; i < N * 3; i++) scl[i] = logScaleToLinear(c.scales[i]);
  add('KHR_gaussian_splatting:SCALE', scl, 'VEC3');

  const op = new Float32Array(N);
  for (let i = 0; i < N; i++) op[i] = sigmoid(c.opacities[i]);
  add('KHR_gaussian_splatting:OPACITY', op, 'SCALAR');

  add('KHR_gaussian_splatting:SH_DEGREE_0_COEF_0', c.shDc.slice(), 'VEC3');

  const shDeg = cloudShDegree(c);
  if (shDeg > 0 && c.shRest) {
    for (let d = 1; d <= shDeg; d++) {
      const colOff = KHR_SH_COL_OFFSET[d];
      for (let ci = 0; ci < KHR_SH_NCOEF[d]; ci++) {
        const coeff = new Float32Array(N * 3);
        for (let i = 0; i < N; i++)
          for (let k = 0; k < 3; k++)
            coeff[i*3+k] = c.shRest[i * c.shK + colOff + 3*ci + k];
        add(`KHR_gaussian_splatting:SH_DEGREE_${d}_COEF_${ci}`, coeff, 'VEC3');
      }
    }
  }

  let bin = new Uint8Array(bufLen);
  { let o = 0; for (const p of bufParts) { bin.set(p, o); o += p.length; } }
  const pad4 = (u8, padByte) => {
    const rem = u8.length % 4;
    if (rem === 0) return u8;
    const out = new Uint8Array(u8.length + 4 - rem);
    out.set(u8); out.fill(padByte, u8.length);
    return out;
  };
  bin = pad4(bin, 0);

  const gltf = {
    asset: { version: '2.0', generator: 'Gaussian Splat Converter' },
    extensionsUsed: ['KHR_gaussian_splatting'],
    extensionsRequired: ['KHR_gaussian_splatting'],
    scene: 0, scenes: [{ nodes: [0] }], nodes: [{ mesh: 0 }],
    meshes: [{ primitives: [{ mode: 0, attributes: primAttrs,
      extensions: { KHR_gaussian_splatting: { kernel: 'ellipse', colorSpace: 'lin_rec709_display' } } }] }],
    accessors: accList, bufferViews: bvList,
    buffers: [{ byteLength: bin.length }],
  };
  const jsonBytes = pad4(new TextEncoder().encode(JSON.stringify(gltf)), 0x20);

  const totalLen = 12 + 8 + jsonBytes.length + 8 + bin.length;
  const out = new Uint8Array(totalLen);
  const dv = new DataView(out.buffer);
  dv.setUint32(0, GLB_MAGIC, true); dv.setUint32(4, 2, true); dv.setUint32(8, totalLen, true);
  dv.setUint32(12, jsonBytes.length, true); dv.setUint32(16, GLB_JSON, true);
  out.set(jsonBytes, 20);
  const bo = 20 + jsonBytes.length;
  dv.setUint32(bo, bin.length, true); dv.setUint32(bo + 4, GLB_BIN, true);
  out.set(bin, bo + 8);
  return out;
}

/* â”€â”€â”€ Dispatch â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€ */

function detectFormat(name) {
  const n = name.toLowerCase();
  if (n.endsWith('.compressed.ply')) return 'compressed_ply';
  if (n.endsWith('.ply'))    return 'ply';
  if (n.endsWith('.splat'))  return 'splat';
  if (n.endsWith('.ksplat')) return 'ksplat';
  if (n.endsWith('.spz'))    return 'spz';
  if (n.endsWith('.sog'))    return 'sog';
  if (n.endsWith('.glb') || n.endsWith('.gltf')) return 'glb';
  return null;
}

/** True when bytes are Niantic SPZ (Format B gzip, or Format A NGSP header). */
function bytesLookLikeSpz(u8) {
  if (!u8 || u8.length < 4) return false;
  // Format B: entire file is gzip(header+payload) — Scaniverse / Niantic v1–3.
  if (u8[0] === 0x1f && u8[1] === 0x8b) return true;
  // Format A / v4: plaintext NGSP ('NGSP' LE = 0x5053474E) header.
  const mag = u8[0] | (u8[1] << 8) | (u8[2] << 16) | (u8[3] << 24);
  return mag === SPZ_MAGIC;
}

/**
 * Sniff on-disk layout from bytes first. Extension is a fallback only.
 * Critical: editor rewrites opened .spz → compressed PLY blobs but may keep a
 * `.spz` filename — trusting the extension would mis-read / passthrough and
 * wash colors (display chunk RGB fed through colorScale as if f_dc).
 */
function detectFormatFromBytes(u8, name) {
  const extFmt = detectFormat(name || 'scene.ply');
  if (!u8 || !u8.length) return extFmt || 'ply';
  if (bytesLookLikeSpz(u8)) return 'spz';
  // ZIP → SOG when extension says so (scene zips are handled elsewhere).
  if (u8[0] === 0x50 && u8[1] === 0x4b && extFmt === 'sog') return 'sog';
  const head = new TextDecoder('ascii').decode(
    u8.subarray(0, Math.min(u8.length, 65536)),
  ).toLowerCase();
  if (head.includes('format ascii')) return 'ascii_ply';
  if (head.includes('element chunk') && head.includes('element vertex')) return 'compressed_ply';
  if (head.startsWith('ply')) return 'ply';
  // GLB binary magic "glTF"
  if (u8[0] === 0x67 && u8[1] === 0x6c && u8[2] === 0x54 && u8[3] === 0x46) return 'glb';
  return extFmt || 'ply';
}

const READERS = {
  ply: readPly, compressed_ply: readCompressedPly, splat: readSplat,
  ksplat: readKsplat, spz: readSpz, sog: readSog, glb: readGlb,
};
const WRITERS = {
  ply: writePly, compressed_ply: writeCompressedPly, splat: writeSplat,
  ksplat: writeKsplat, spz: writeSpz, sog: writeSog, glb: writeGlb,
};
const FORMAT_EXT = {
  ply: '.ply', compressed_ply: '.compressed.ply', splat: '.splat',
  ksplat: '.ksplat', spz: '.spz', sog: '.sog', glb: '.glb',
};

/* Read input bytes, convert, return { bytes, count, shDegree }.
 * opts: { shDegree (ply output only), chunkSize (compressed_ply), zipLevel (sog),
 *         clampAnisotropy (max axis ratio; default 8 when true/number) } */
async function convert(bytes, srcFmt, dstFmt, opts = {}) {
  bytes = ensureBytes(bytes);
  const cloud = await READERS[srcFmt](bytes);
  const count = cloud.count;
  if (dstFmt === 'ply' && (opts.shDegree ?? 3) < 3)
    truncateSh(cloud, opts.shDegree);
  if (opts.clampAnisotropy != null && opts.clampAnisotropy !== false) {
    const lim = opts.clampAnisotropy === true ? 8 : +opts.clampAnisotropy;
    if (Number.isFinite(lim) && lim >= 1) clampCloudAnisotropy(cloud, lim);
  }
  let out;
  if (dstFmt === 'compressed_ply') out = WRITERS.compressed_ply(cloud, opts.chunkSize || 256);
  else if (dstFmt === 'sog') out = await WRITERS.sog(cloud, opts.zipLevel || 5);
  else out = await WRITERS[dstFmt](cloud);
  return { bytes: out, count, shDegree: cloudShDegree(cloud) };
}

globalThis.SplatConvert = {
  detectFormat, detectFormatFromBytes, bytesLookLikeSpz, READERS, WRITERS, FORMAT_EXT, convert,
  truncateSh, clampCloudAnisotropy,
  makeCloud, normalizeRotations, cloudShDegree, mortonOrder, transformCloud,
  decodeImageRgba,                 // shared with mesh_convert.js
  _internal: {
    SH_C0, SPZ_COLOR_SCALE, logit, sigmoid, clamp,
    rgbToShDc, shDcToDisplay, shDcToRgb, packShDcToU8, unpackU8ToShDc,
    linearScaleToLog, logScaleToLinear, LOG_SCALE_FLOOR,
    apply180XPos, apply180XQuatWxyz,
    spzShDcToByte, spzByteToShDc, bytesLookLikeSpz,
    compressedPlyVerticesPerChunk,
    cplyPackRotation, cplyUnpackRotation,
    clampCloudAnisotropy,
  },
};

})();
