/* =========================================================
   EXAMGUARD - MATH, DIAGRAM AND GRAPH RENDERER
   ---------------------------------------------------------
   Teachers type plain text; this turns it into proper math.
   Nothing here touches the database: the tags live inside the
   normal question text, so old and new questions both work.

   TEXT SYNTAX
     x^2  x_1  x^(n+1)        powers and subscripts
     {a/b}                    stacked fraction
     sqrt(x+1)                square root
     d/dx   dy/dx   d^2y/dx^2 derivative as a fraction
     f'(x)                    prime (just type the apostrophe)
     int[0,2] 3x^2 dx         definite integral   (int = indefinite)
     sum[i=1,n]   lim[x->2]   summation, limit
     pi theta alpha beta delta inf  ->  symbols
     <=  >=  !=  +-  ->  45deg
   DIAGRAM / GRAPH TAGS (drawn as pictures)
     [[angle: 60]]   [[angle: ?, label=x]]
     [[triangle: b=6, h=4, unit=cm]]    [[triangle: a=3, b=4, c=5]]
     [[rect: l=8, w=5, unit=cm]]        [[circle: r=5]]
     [[prism: l=6, w=4, h=3, unit=cm]]  [[cube: s=4]]
     [[cylinder: r=3, h=8]]  [[cone: r=3, h=8, l=?]]  [[sphere: r=5]]
     [[trapezoid: a=4, b=8, h=3, unit=cm]]
     [[graph: x^2 - 4; -5..5]]          [[graph: x^2, 2x+1; -3..3]]
     [[graph: x^2; -3..3; shade=0..2]]  (shade = area under curve)
     [[img: https://example.com/picture.png]]   (or use "Upload photo")
   ========================================================= */

(function () {

  "use strict";

  var INK = "#172033";
  var BLUE = "#315efb";
  var FILL = "rgba(49,94,251,.13)";
  var FILL2 = "rgba(49,94,251,.24)";
  var GRID = "#e3e8f0";
  var COLORS = ["#315efb", "#dc2626", "#16a34a", "#7c3aed"];
  var figureCounter = 0;


  function esc(value) {
    return String(value == null ? "" : value)
      .replace(/&/g, "&amp;")
      .replace(/</g, "&lt;")
      .replace(/>/g, "&gt;")
      .replace(/"/g, "&quot;")
      .replace(/'/g, "&#039;");
  }

  function fmt(n) {
    if (!isFinite(n)) return "";
    var r = Math.round(n * 100) / 100;
    return String(r);
  }

  function clamp(v, lo, hi) {
    return Math.min(hi, Math.max(lo, v));
  }


  /* =======================================================
     EXPRESSION PARSER (safe: no eval) - used by graphs
     ======================================================= */

  var FUNCS = {
    sin: Math.sin, cos: Math.cos, tan: Math.tan,
    asin: Math.asin, acos: Math.acos, atan: Math.atan,
    sqrt: Math.sqrt, abs: Math.abs, exp: Math.exp,
    ln: Math.log, log: function (v) { return Math.log(v) / Math.LN10; }
  };

  function tokenize(src) {

    var tokens = [];
    var i = 0;

    while (i < src.length) {

      var c = src[i];

      if (/\s/.test(c)) { i++; continue; }

      var m = /^(\d+\.?\d*|\.\d+)/.exec(src.slice(i));
      if (m) { tokens.push({ t: "num", v: parseFloat(m[1]) }); i += m[1].length; continue; }

      m = /^(asin|acos|atan|sin|cos|tan|sqrt|abs|exp|ln|log)/.exec(src.slice(i));
      if (m) { tokens.push({ t: "fn", v: m[1] }); i += m[1].length; continue; }

      if (src.slice(i, i + 2) === "pi") { tokens.push({ t: "num", v: Math.PI }); i += 2; continue; }

      if (c === "x" || c === "X") { tokens.push({ t: "var" }); i++; continue; }

      if (c === "e") { tokens.push({ t: "num", v: Math.E }); i++; continue; }

      if ("+-*/^()".indexOf(c) >= 0) { tokens.push({ t: "op", v: c }); i++; continue; }

      throw new Error("unexpected \"" + c + "\"");

    }

    return tokens;

  }

  function compileExpr(source) {

    var src = String(source)
      .replace(/^\s*(?:y|f\(x\)|g\(x\)|h\(x\))\s*=\s*/i, "")
      .replace(/\u2212/g, "-")
      .replace(/\u03c0/g, "pi")
      .replace(/\*\*/g, "^");

    var tokens = tokenize(src);
    var pos = 0;

    function peek() { return tokens[pos]; }
    function isOp(v) { var k = tokens[pos]; return k && k.t === "op" && k.v === v; }

    function parseExpr() {
      var left = parseTerm();
      while (isOp("+") || isOp("-")) {
        var op = tokens[pos++].v;
        var right = parseTerm();
        left = (function (a, b, o) {
          return o === "+" ? function (x) { return a(x) + b(x); }
                           : function (x) { return a(x) - b(x); };
        })(left, right, op);
      }
      return left;
    }

    function startsFactor() {
      var k = peek();
      if (!k) return false;
      if (k.t === "num" || k.t === "var" || k.t === "fn") return true;
      return k.t === "op" && k.v === "(";
    }

    function parseTerm() {
      var left = parseUnary();
      for (;;) {
        var op = null;
        if (isOp("*") || isOp("/")) op = tokens[pos++].v;
        else if (startsFactor()) op = "*";
        else break;
        var right = parseUnary();
        left = (function (a, b, o) {
          return o === "*" ? function (x) { return a(x) * b(x); }
                           : function (x) { return a(x) / b(x); };
        })(left, right, op);
      }
      return left;
    }

    function parseUnary() {
      if (isOp("-")) { pos++; var u = parseUnary(); return function (x) { return -u(x); }; }
      if (isOp("+")) { pos++; return parseUnary(); }
      return parsePower();
    }

    function parsePower() {
      var base = parseAtom();
      if (isOp("^")) {
        pos++;
        var exp = parseUnary();
        return function (x) { return Math.pow(base(x), exp(x)); };
      }
      return base;
    }

    function parseAtom() {
      var k = tokens[pos++];
      if (!k) throw new Error("unfinished expression");
      if (k.t === "num") { var v = k.v; return function () { return v; }; }
      if (k.t === "var") return function (x) { return x; };
      if (k.t === "fn") {
        var f = FUNCS[k.v];
        var arg = isOp("(") ? parseAtom() : parsePower();
        return function (x) { return f(arg(x)); };
      }
      if (k.t === "op" && k.v === "(") {
        var inner = parseExpr();
        if (!isOp(")")) throw new Error("missing )");
        pos++;
        return inner;
      }
      throw new Error("unexpected \"" + (k.v || k.t) + "\"");
    }

    var fn = parseExpr();
    if (pos < tokens.length) throw new Error("unexpected \"" + (tokens[pos].v || tokens[pos].t) + "\"");
    return fn;

  }


  /* =======================================================
     SMALL SVG HELPERS
     ======================================================= */

  function figure(viewW, viewH, inner, label, vbx, vby, scale) {
    vbx = vbx || 0; vby = vby || 0;
    var shownW = Math.round(viewW * (scale || 1.1));
    return '<span class="m-fig"><svg viewBox="' + fmt(vbx) + ' ' + fmt(vby) + ' ' + fmt(viewW) + ' ' + fmt(viewH) +
      '" width="' + shownW + '" role="img" aria-label="' + esc(label) +
      '" xmlns="http://www.w3.org/2000/svg" font-family="Inter, Arial, sans-serif" font-size="13">' +
      inner + '</svg></span>';
  }

  function line(x1, y1, x2, y2, extra) {
    return '<line x1="' + x1 + '" y1="' + y1 + '" x2="' + x2 + '" y2="' + y2 +
      '" stroke="' + INK + '" stroke-width="1.6" stroke-linecap="round" ' + (extra || "") + '/>';
  }

  function text(x, y, str, anchor, extra) {
    extra = extra || "";
    return '<text x="' + x + '" y="' + y + '" text-anchor="' + (anchor || "middle") + '" ' +
      (extra.indexOf("fill=") >= 0 ? "" : 'fill="' + INK + '" ') + extra + '>' + esc(str) + '</text>';
  }

  function dimLabel(kv, key, name, unit) {
    var v = kv[key];
    if (v === undefined || v === "") return name;
    if (v === "?") return "?";
    return v + (unit ? " " + unit : "");
  }

  function dimNum(kv, key, fallback) {
    var n = parseFloat(kv[key]);
    return isFinite(n) && n > 0 ? n : fallback;
  }

  function parseParams(body) {
    var out = { pos: [], kv: {} };
    String(body).split(",").forEach(function (part) {
      part = part.trim();
      if (!part) return;
      var i = part.indexOf("=");
      if (i > 0) out.kv[part.slice(0, i).trim().toLowerCase()] = part.slice(i + 1).trim();
      else out.pos.push(part);
    });
    return out;
  }

  function rightMark(x, y, dirX, dirY, s) {
    /* small square at corner (x,y) opening toward dirX/dirY */
    x = +x; y = +y;
    return '<path d="M ' + (x + dirX * s) + ' ' + y +
      ' L ' + (x + dirX * s) + ' ' + (y + dirY * s) +
      ' L ' + x + ' ' + (y + dirY * s) +
      '" fill="none" stroke="' + INK + '" stroke-width="1.2"/>';
  }


  /* =======================================================
     DIAGRAMS
     ======================================================= */

  function svgAngle(p) {

    var raw = p.pos.length ? p.pos[0] : (p.kv.deg || p.kv.angle || "?");
    var num = parseFloat(raw);
    var known = isFinite(num);
    var drawn = known
      ? clamp(num, 8, 352)
      : (isFinite(parseFloat(p.kv.draw)) ? parseFloat(p.kv.draw) : 55);
    var label = p.kv.label || "";
    var caption = known
      ? (label ? label + " = " : "") + fmt(num) + "\u00b0"
      : (label || "?");

    var vx = 110, vy = 110, len = 95, r = 32;
    var rad = drawn * Math.PI / 180;
    var ex = vx + len * Math.cos(rad);
    var ey = vy - len * Math.sin(rad);

    var arc;
    if (Math.abs(drawn - 90) < 0.5) {
      arc = '<path d="M ' + (vx + 14) + ' ' + vy + ' L ' + (vx + 14) + ' ' + (vy - 14) +
        ' L ' + vx + ' ' + (vy - 14) + '" fill="none" stroke="' + INK + '" stroke-width="1.3"/>';
    } else {
      var ax = vx + r * Math.cos(rad);
      var ay = vy - r * Math.sin(rad);
      arc = '<path d="M ' + (vx + r) + ' ' + vy + ' A ' + r + ' ' + r + ' 0 ' +
        (drawn > 180 ? 1 : 0) + ' 0 ' + fmt(ax) + ' ' + fmt(ay) +
        '" fill="' + FILL + '" stroke="' + BLUE + '" stroke-width="1.6"/>';
    }

    var mid = rad / 2;
    var lx = vx + (r + 22) * Math.cos(mid);
    var ly = vy - (r + 22) * Math.sin(mid) + 4;

    var inner =
      arc +
      line(vx, vy, vx + len, vy) +
      line(vx, vy, fmt(ex), fmt(ey)) +
      '<circle cx="' + vx + '" cy="' + vy + '" r="2.6" fill="' + INK + '"/>' +
      text(fmt(lx), fmt(ly), caption, "middle", 'font-weight="600"');

    var pad = 14;
    var xs = [vx, vx + len, ex, lx - 26, lx + 26];
    var ys = [vy, ey, ly - 14, ly + 6];
    if (drawn > 180) ys.push(vy + len * Math.abs(Math.sin(rad)));
    var bx0 = Math.min.apply(null, xs) - pad, bx1 = Math.max.apply(null, xs) + pad;
    var by0 = Math.min.apply(null, ys) - pad, by1 = Math.max.apply(null, ys) + pad;

    return figure(bx1 - bx0, by1 - by0, inner, "Angle diagram: " + caption, bx0, by0, 1.5);

  }


  function svgTriangle(p) {

    var kv = p.kv;
    var unit = kv.unit || "";
    var inner = "";

    if (kv.h !== undefined) {

      /* base + height (for area) */
      var B = dimNum(kv, "b", 6), H = dimNum(kv, "h", 4);
      var ratio = clamp(H / B, 0.3, 1.2);
      var bw = 190, bh = bw * ratio;
      var x0 = 25, y0 = 190 - (140 - Math.min(bh, 140)) * 0;
      bh = Math.min(bh, 140);
      var apexX = x0 + bw * 0.34;
      var apexY = y0 - bh;

      inner =
        '<polygon points="' + x0 + ',' + y0 + ' ' + (x0 + bw) + ',' + y0 + ' ' + fmt(apexX) + ',' + fmt(apexY) +
        '" fill="' + FILL + '" stroke="' + INK + '" stroke-width="1.6" stroke-linejoin="round"/>' +
        line(fmt(apexX), fmt(apexY), fmt(apexX), y0, 'stroke-dasharray="5 4"') +
        rightMark(fmt(apexX), y0, 1, -1, 10) +
        text(x0 + bw / 2, y0 + 18, dimLabel(kv, "b", "b", unit)) +
        text(fmt(apexX + 8), fmt(y0 - bh / 2 + 4), dimLabel(kv, "h", "h", unit), "start");

      return figure(240, 215, inner, "Triangle with base and height");

    }

    /* three sides */
    var a = dimNum(kv, "a", 5), b = dimNum(kv, "b", 4), c = dimNum(kv, "c", 3);
    if (a + b <= c || a + c <= b || b + c <= a) { a = 5; b = 4; c = 3; }

    var cx = (b * b + c * c - a * a) / (2 * c);
    var cy = Math.sqrt(Math.max(b * b - cx * cx, 0.0001));
    var minX = Math.min(0, cx), maxX = Math.max(c, cx);
    var scale = Math.min(190 / (maxX - minX), 130 / cy);
    var ox = 25 - minX * scale + (190 - (maxX - minX) * scale) / 2;
    var oy = 185;

    var A = [ox, oy];
    var Bp = [ox + c * scale, oy];
    var C = [ox + cx * scale, oy - cy * scale];
    var cen = [(A[0] + Bp[0] + C[0]) / 3, (A[1] + Bp[1] + C[1]) / 3];

    function sideLabel(P, Q, str) {
      var mx = (P[0] + Q[0]) / 2, my = (P[1] + Q[1]) / 2;
      var dx = mx - cen[0], dy = my - cen[1];
      var d = Math.sqrt(dx * dx + dy * dy) || 1;
      var ux = dx / d, uy = dy / d;
      var anchor = ux > 0.45 ? "start" : ux < -0.45 ? "end" : "middle";
      return text(fmt(mx + ux * 10), fmt(my + uy * 14 + 4), str, anchor);
    }

    inner =
      '<polygon points="' + A.map(fmt).join(",") + " " + Bp.map(fmt).join(",") + " " + C.map(fmt).join(",") +
      '" fill="' + FILL + '" stroke="' + INK + '" stroke-width="1.6" stroke-linejoin="round"/>' +
      sideLabel(A, Bp, dimLabel(kv, "c", "c", unit)) +
      sideLabel(A, C, dimLabel(kv, "b", "b", unit)) +
      sideLabel(Bp, C, dimLabel(kv, "a", "a", unit));

    return figure(240, 215, inner, "Triangle with three sides");

  }


  function svgRect(p) {

    var kv = p.kv, unit = kv.unit || "";
    var L = dimNum(kv, "l", dimNum(kv, "b", 8)), W = dimNum(kv, "w", dimNum(kv, "h", 5));
    var ratio = clamp(W / L, 0.25, 1.2);
    var w = 190, h = Math.min(w * ratio, 140);
    var x0 = 25, y0 = 20;

    var inner =
      '<rect x="' + x0 + '" y="' + y0 + '" width="' + w + '" height="' + fmt(h) +
      '" fill="' + FILL + '" stroke="' + INK + '" stroke-width="1.6"/>' +
      text(x0 + w / 2, y0 + h + 19, dimLabel(kv, kv.l !== undefined ? "l" : "b", "l", unit)) +
      text(x0 + w + 8, fmt(y0 + h / 2 + 4), dimLabel(kv, kv.w !== undefined ? "w" : "h", "w", unit), "start");

    return figure(260, Math.ceil(y0 + h + 30), inner, "Rectangle");

  }


  function svgCircle(p) {

    var kv = p.kv, unit = kv.unit || "";
    var cx = 120, cy = 100, r = 75;
    var useD = kv.d !== undefined && kv.r === undefined;

    var inner =
      '<circle cx="' + cx + '" cy="' + cy + '" r="' + r + '" fill="' + FILL + '" stroke="' + INK + '" stroke-width="1.6"/>';

    if (useD) {
      inner += line(cx - r, cy, cx + r, cy) +
        text(cx, cy - 8, dimLabel(kv, "d", "d", unit));
    } else {
      inner += line(cx, cy, cx + r, cy) +
        text(cx + r / 2, cy - 8, dimLabel(kv, "r", "r", unit));
    }

    inner += '<circle cx="' + cx + '" cy="' + cy + '" r="2.6" fill="' + INK + '"/>';

    return figure(240, 205, inner, "Circle");

  }


  function svgPrism(p, isCube) {

    var kv = p.kv, unit = kv.unit || "";

    var l, w, h;
    if (isCube) {
      var s = dimNum(kv, "s", dimNum(kv, "l", 4));
      l = w = h = s;
    } else {
      l = dimNum(kv, "l", 6); w = dimNum(kv, "w", 4); h = dimNum(kv, "h", 3);
    }

    var mx = Math.max(l, w, h);
    var nl = Math.max(l / mx, 0.3), nw = Math.max(w / mx, 0.3), nh = Math.max(h / mx, 0.3);

    var sc = 130;
    var fw = nl * sc, fh = nh * sc;
    var dd = nw * sc * 0.5;

    var x0 = 30, y0 = 40 + dd + fh;              /* front bottom-left */
    var X = function (n) { return fmt(n); };

    var fbl = [x0, y0], fbr = [x0 + fw, y0], ftl = [x0, y0 - fh], ftr = [x0 + fw, y0 - fh];
    var bbl = [x0 + dd, y0 - dd], bbr = [x0 + fw + dd, y0 - dd];
    var btl = [x0 + dd, y0 - fh - dd], btr = [x0 + fw + dd, y0 - fh - dd];

    function pts(arr) { return arr.map(function (q) { return X(q[0]) + "," + X(q[1]); }).join(" "); }
    var edge = 'fill="' + FILL + '" stroke="' + INK + '" stroke-width="1.6" stroke-linejoin="round"';

    var inner =
      /* hidden edges */
      line(X(bbl[0]), X(bbl[1]), X(fbl[0]), X(fbl[1]), 'stroke-dasharray="5 4" stroke-width="1.1"') +
      line(X(bbl[0]), X(bbl[1]), X(bbr[0]), X(bbr[1]), 'stroke-dasharray="5 4" stroke-width="1.1"') +
      line(X(bbl[0]), X(bbl[1]), X(btl[0]), X(btl[1]), 'stroke-dasharray="5 4" stroke-width="1.1"') +
      /* faces */
      '<polygon points="' + pts([ftl, ftr, btr, btl]) + '" ' + 'fill="' + FILL2 + '" stroke="' + INK + '" stroke-width="1.6" stroke-linejoin="round"/>' +
      '<polygon points="' + pts([ftr, fbr, bbr, btr]) + '" ' + 'fill="rgba(49,94,251,.06)" stroke="' + INK + '" stroke-width="1.6" stroke-linejoin="round"/>' +
      '<polygon points="' + pts([fbl, fbr, ftr, ftl]) + '" ' + edge + '/>' +
      /* labels */
      text(X(x0 + fw / 2), X(y0 + 19), dimLabel(kv, isCube ? "s" : "l", isCube ? "s" : "l", unit)) +
      text(X(x0 - 8), X(y0 - fh / 2 + 4), dimLabel(kv, isCube ? "s" : "h", isCube ? "s" : "h", unit), "end") +
      text(X(x0 + fw + dd / 2 + 8), X(y0 - dd / 2 + 16), dimLabel(kv, isCube ? "s" : "w", isCube ? "s" : "w", unit), "start");

    return figure(280, Math.ceil(y0 + 30), inner, isCube ? "Cube" : "Rectangular prism");

  }


  function svgCylinder(p) {

    var kv = p.kv, unit = kv.unit || "";
    var R = dimNum(kv, "r", 3), H = dimNum(kv, "h", 8);

    var rx = 50;
    var ry = 20;
    var hpx = clamp(rx * (H / R) * 0.9, 55, 150);

    var cx = 100, top = 30;
    var bot = top + hpx;

    var inner =
      /* body */
      '<path d="M ' + (cx - rx) + ' ' + top + ' L ' + (cx - rx) + ' ' + bot +
      ' A ' + rx + ' ' + ry + ' 0 0 0 ' + (cx + rx) + ' ' + bot +
      ' L ' + (cx + rx) + ' ' + top + '" fill="' + FILL + '" stroke="' + INK + '" stroke-width="1.6"/>' +
      /* hidden back of the base */
      '<path d="M ' + (cx - rx) + ' ' + bot + ' A ' + rx + ' ' + ry + ' 0 0 1 ' + (cx + rx) + ' ' + bot +
      '" fill="none" stroke="' + INK + '" stroke-width="1.1" stroke-dasharray="5 4"/>' +
      /* top */
      '<ellipse cx="' + cx + '" cy="' + top + '" rx="' + rx + '" ry="' + ry + '" fill="' + FILL2 + '" stroke="' + INK + '" stroke-width="1.6"/>' +
      line(cx, top, cx + rx, top, 'stroke-dasharray="4 3" stroke-width="1.2"') +
      '<circle cx="' + cx + '" cy="' + top + '" r="2.4" fill="' + INK + '"/>' +
      text(cx + rx / 2, top + 15, dimLabel(kv, "r", "r", unit), "middle", 'font-size="11"') +
      /* height */
      line(cx + rx + 16, top, cx + rx + 16, bot, 'stroke-width="1.2"') +
      line(cx + rx + 11, top, cx + rx + 21, top, 'stroke-width="1.2"') +
      line(cx + rx + 11, bot, cx + rx + 21, bot, 'stroke-width="1.2"') +
      text(cx + rx + 26, fmt((top + bot) / 2 + 4), dimLabel(kv, "h", "h", unit), "start");

    return figure(240, Math.ceil(bot + ry + 14), inner, "Cylinder");

  }



  function svgCone(p) {

    var kv = p.kv, unit = kv.unit || "";
    var R = dimNum(kv, "r", 3), H = dimNum(kv, "h", 8);

    var rx = 50, ry = 20;
    var hpx = clamp(rx * (H / R) * 0.9, 60, 150);
    var cx = 125, top = 20;
    var base = top + hpx;
    var dimX = cx - rx - 16;

    var inner =
      '<path d="M ' + cx + ' ' + top + ' L ' + (cx - rx) + ' ' + base +
      ' A ' + rx + ' ' + ry + ' 0 0 0 ' + (cx + rx) + ' ' + base + ' Z" fill="' + FILL + '" stroke="' + INK + '" stroke-width="1.6" stroke-linejoin="round"/>' +
      '<path d="M ' + (cx - rx) + ' ' + base + ' A ' + rx + ' ' + ry + ' 0 0 1 ' + (cx + rx) + ' ' + base +
      '" fill="none" stroke="' + INK + '" stroke-width="1.1" stroke-dasharray="5 4"/>' +
      line(cx, top, cx, base, 'stroke-dasharray="5 4" stroke-width="1.2"') +
      line(cx, base, cx + rx, base, 'stroke-dasharray="4 3" stroke-width="1.2"') +
      '<circle cx="' + cx + '" cy="' + base + '" r="2.4" fill="' + INK + '"/>' +
      /* height dimension line on the left */
      line(dimX, top, dimX, base, 'stroke-width="1.2"') +
      line(dimX - 5, top, dimX + 5, top, 'stroke-width="1.2"') +
      line(dimX - 5, base, dimX + 5, base, 'stroke-width="1.2"') +
      text(dimX - 8, fmt((top + base) / 2 + 4), dimLabel(kv, "h", "h", unit), "end") +
      text(cx + rx / 2, base + 14, dimLabel(kv, "r", "r", unit), "middle", 'font-size="11"');

    if (kv.l !== undefined) {
      inner += text(fmt(cx + rx / 2 + 10), fmt((top + base) / 2 - 2), dimLabel(kv, "l", "l", unit), "start");
    }

    return figure(260, Math.ceil(base + ry + 14), inner, "Cone");

  }


  function svgSphere(p) {

    var kv = p.kv, unit = kv.unit || "";
    var cx = 110, cy = 92, r = 72, ry = 22;
    var useD = kv.d !== undefined && kv.r === undefined;

    var inner =
      '<circle cx="' + cx + '" cy="' + cy + '" r="' + r + '" fill="' + FILL + '" stroke="' + INK + '" stroke-width="1.6"/>' +
      '<path d="M ' + (cx - r) + ' ' + cy + ' A ' + r + ' ' + ry + ' 0 0 0 ' + (cx + r) + ' ' + cy +
      '" fill="none" stroke="' + INK + '" stroke-width="1.1"/>' +
      '<path d="M ' + (cx - r) + ' ' + cy + ' A ' + r + ' ' + ry + ' 0 0 1 ' + (cx + r) + ' ' + cy +
      '" fill="none" stroke="' + INK + '" stroke-width="1.1" stroke-dasharray="5 4"/>';

    if (useD) {
      inner += line(cx - r, cy, cx + r, cy, 'stroke-width="1.4"') +
        text(cx, cy + 16, dimLabel(kv, "d", "d", unit), "middle", 'font-size="12"');
    } else {
      inner += line(cx, cy, cx + r, cy, 'stroke-width="1.4"') +
        text(cx + r / 2, cy + 16, dimLabel(kv, "r", "r", unit), "middle", 'font-size="12"');
    }

    inner += '<circle cx="' + cx + '" cy="' + cy + '" r="2.6" fill="' + INK + '"/>';

    return figure(220, 190, inner, "Sphere");

  }


  function svgTrapezoid(p) {

    var kv = p.kv, unit = kv.unit || "";
    var A = dimNum(kv, "a", 4), B = dimNum(kv, "b", 8), H = dimNum(kv, "h", 4);

    var widest = Math.max(A, B);
    var scale = 200 / widest;
    var bw = B * scale, aw = A * scale;
    var hp = clamp(H * scale, 50, 130);

    var x0 = 30, y0 = 28 + hp;
    var bx = x0 + (200 - bw) / 2, tx = x0 + (200 - aw) / 2;

    var BL = [bx, y0], BR = [bx + bw, y0], TR = [tx + aw, y0 - hp], TL = [tx, y0 - hp];

    function pts(arr) { return arr.map(function (q) { return fmt(q[0]) + "," + fmt(q[1]); }).join(" "); }

    var inner =
      '<polygon points="' + pts([BL, BR, TR, TL]) + '" fill="' + FILL + '" stroke="' + INK + '" stroke-width="1.6" stroke-linejoin="round"/>' +
      line(fmt(TL[0]), fmt(TL[1]), fmt(TL[0]), fmt(y0), 'stroke-dasharray="5 4" stroke-width="1.2"') +
      rightMark(fmt(TL[0]), y0, TL[0] >= BL[0] ? 1 : -1, -1, 9) +
      text(fmt((TL[0] + TR[0]) / 2), fmt(TL[1] - 8), dimLabel(kv, "a", "a", unit)) +
      text(fmt((BL[0] + BR[0]) / 2), fmt(y0 + 19), dimLabel(kv, "b", "b", unit)) +
      text(fmt(TL[0] + 7), fmt(y0 - hp / 2 + 4), dimLabel(kv, "h", "h", unit), "start");

    if (kv.c !== undefined) {
      inner += text(fmt((TR[0] + BR[0]) / 2 + 8), fmt(y0 - hp / 2 + 4), dimLabel(kv, "c", "c", unit), "start");
      inner += text(fmt((TL[0] + BL[0]) / 2 - 8), fmt(y0 - hp / 2 + 4), dimLabel(kv, "c", "c", unit), "end");
    }

    return figure(260, Math.ceil(y0 + 30), inner, "Trapezoid");

  }


  /* =======================================================
     GRAPHS
     ======================================================= */

  function niceStep(range) {
    var raw = range / 6;
    var mag = Math.pow(10, Math.floor(Math.log(raw) / Math.LN10));
    var n = raw / mag;
    return (n < 1.5 ? 1 : n < 3 ? 2 : n < 7 ? 5 : 10) * mag;
  }

  var RANGE_RE = /^(-?\d+(?:\.\d+)?)\s*\.\.\s*(-?\d+(?:\.\d+)?)$/;

  function svgGraph(body) {

    var parts = body.split(";").map(function (s) { return s.trim(); }).filter(Boolean);
    if (!parts.length) throw new Error("no function given");

    var exprs = parts[0].split(",").map(function (s) { return s.trim(); }).filter(Boolean);
    var fns = exprs.map(compileExpr);

    var xmin = -5, xmax = 5, yFixed = null, shade = null;

    var seenX = false;
    parts.slice(1).forEach(function (item) {
      var m;
      if ((m = /^y\s*=\s*(.+)$/i.exec(item)) && RANGE_RE.test(m[1].trim())) {
        var r = RANGE_RE.exec(m[1].trim());
        yFixed = [parseFloat(r[1]), parseFloat(r[2])];
      } else if ((m = /^shade\s*=\s*(.+)$/i.exec(item)) && RANGE_RE.test(m[1].trim())) {
        var s = RANGE_RE.exec(m[1].trim());
        shade = [parseFloat(s[1]), parseFloat(s[2])];
      } else if (!seenX && RANGE_RE.test(item)) {
        var q = RANGE_RE.exec(item);
        xmin = parseFloat(q[1]); xmax = parseFloat(q[2]);
        seenX = true;
      }
    });

    if (!(xmax > xmin)) { xmin = -5; xmax = 5; }

    var N = 360;
    var samples = fns.map(function (f) {
      var arr = [];
      for (var i = 0; i <= N; i++) {
        var x = xmin + (xmax - xmin) * i / N;
        var y = f(x);
        arr.push([x, isFinite(y) ? y : NaN]);
      }
      return arr;
    });

    var ymin, ymax;

    if (yFixed && yFixed[1] > yFixed[0]) {
      ymin = yFixed[0]; ymax = yFixed[1];
    } else {
      var vals = [];
      samples.forEach(function (arr) {
        arr.forEach(function (pt) { if (isFinite(pt[1]) && Math.abs(pt[1]) < 1e6) vals.push(pt[1]); });
      });
      if (!vals.length) throw new Error("nothing to plot in that range");
      vals.sort(function (a, b) { return a - b; });
      var lo = vals[Math.floor(vals.length * 0.02)];
      var hi = vals[Math.min(vals.length - 1, Math.ceil(vals.length * 0.98) - 1)];
      if (hi - lo < 1e-9) { lo -= 1; hi += 1; }
      if (lo > 0 && lo < (hi - lo)) lo = 0;
      if (hi < 0 && -hi < (hi - lo)) hi = 0;
      var pad = (hi - lo) * 0.1;
      ymin = lo - pad; ymax = hi + pad;
      var st = niceStep(ymax - ymin);
      ymin = Math.floor(ymin / st) * st;
      ymax = Math.ceil(ymax / st) * st;
    }

    var W = 360, H = 260, ml = 36, mr = 14, mt = 14, mb = 26;
    var pw = W - ml - mr, ph = H - mt - mb;

    function px(x) { return ml + (x - xmin) / (xmax - xmin) * pw; }
    function py(y) { return mt + (1 - (y - ymin) / (ymax - ymin)) * ph; }

    var id = "mclip" + (++figureCounter);

    var out = '<defs><clipPath id="' + id + '"><rect x="' + ml + '" y="' + mt + '" width="' + pw + '" height="' + ph + '"/></clipPath></defs>';

    /* grid + tick labels */
    var xs = niceStep(xmax - xmin), ys = niceStep(ymax - ymin);

    function ticks(a, b, step) {
      var res = [];
      var t = Math.ceil(a / step - 1e-9) * step;
      for (; t <= b + 1e-9; t += step) res.push(Math.round(t / step) * step);
      return res;
    }

    ticks(xmin, xmax, xs).forEach(function (t) {
      out += '<line x1="' + fmt(px(t)) + '" y1="' + mt + '" x2="' + fmt(px(t)) + '" y2="' + (mt + ph) + '" stroke="' + GRID + '" stroke-width="1"/>';
      if (Math.abs(t) > 1e-9) out += text(fmt(px(t)), mt + ph + 15, fmt(t), "middle", 'font-size="10" fill="#667085"');
    });

    ticks(ymin, ymax, ys).forEach(function (t) {
      out += '<line x1="' + ml + '" y1="' + fmt(py(t)) + '" x2="' + (ml + pw) + '" y2="' + fmt(py(t)) + '" stroke="' + GRID + '" stroke-width="1"/>';
      if (Math.abs(t) > 1e-9) out += text(ml - 5, fmt(py(t) + 3.5), fmt(t), "end", 'font-size="10" fill="#667085"');
    });

    /* frame + axes */
    out += '<rect x="' + ml + '" y="' + mt + '" width="' + pw + '" height="' + ph + '" fill="none" stroke="#c9d1de" stroke-width="1"/>';

    if (ymin <= 0 && ymax >= 0) out += line(ml, fmt(py(0)), ml + pw, fmt(py(0)), 'stroke-width="1.4"');
    if (xmin <= 0 && xmax >= 0) out += line(fmt(px(0)), mt, fmt(px(0)), mt + ph, 'stroke-width="1.4"');

    if (ymin <= 0 && ymax >= 0) out += text(ml + pw - 4, fmt(py(0) - 5), "x", "end", 'font-style="italic" font-size="11"');
    if (xmin <= 0 && xmax >= 0) out += text(fmt(px(0) + 8), mt + 10, "y", "start", 'font-style="italic" font-size="11"');

    /* shaded area under the first curve */
    if (shade) {
      var a = clamp(Math.min(shade[0], shade[1]), xmin, xmax);
      var b = clamp(Math.max(shade[0], shade[1]), xmin, xmax);
      var poly = [];
      var M = 120;
      var f0 = fns[0];
      var zeroY = clamp(0, ymin, ymax);
      poly.push(fmt(px(a)) + "," + fmt(py(zeroY)));
      for (var k = 0; k <= M; k++) {
        var xx = a + (b - a) * k / M;
        var yy = f0(xx);
        if (isFinite(yy)) poly.push(fmt(px(xx)) + "," + fmt(py(clamp(yy, ymin - (ymax - ymin), ymax + (ymax - ymin)))));
      }
      poly.push(fmt(px(b)) + "," + fmt(py(zeroY)));
      out += '<polygon clip-path="url(#' + id + ')" points="' + poly.join(" ") + '" fill="rgba(49,94,251,.22)" stroke="none"/>';
      out += line(fmt(px(a)), fmt(py(zeroY)), fmt(px(a)), fmt(py(f0(a) || 0)), 'stroke-dasharray="4 3" stroke-width="1.1" clip-path="url(#' + id + ')"');
      out += line(fmt(px(b)), fmt(py(zeroY)), fmt(px(b)), fmt(py(f0(b) || 0)), 'stroke-dasharray="4 3" stroke-width="1.1" clip-path="url(#' + id + ')"');
    }

    /* curves */
    var span = ymax - ymin;

    samples.forEach(function (arr, idx) {
      var d = "", pen = false, prev = null;
      arr.forEach(function (pt) {
        var y = pt[1];
        if (!isFinite(y) || Math.abs(y) > span * 20) { pen = false; prev = null; return; }
        if (prev !== null && Math.abs(y - prev) > span * 0.9 && (y > 0) !== (prev > 0)) pen = false;
        d += (pen ? " L " : " M ") + fmt(px(pt[0])) + " " + fmt(py(y));
        pen = true;
        prev = y;
      });
      out += '<path clip-path="url(#' + id + ')" d="' + d + '" fill="none" stroke="' + COLORS[idx % COLORS.length] + '" stroke-width="2.2" stroke-linejoin="round" stroke-linecap="round"/>';
    });

    /* legend when several curves */
    if (exprs.length > 1) {
      exprs.forEach(function (e, idx) {
        var ly = mt + 14 + idx * 14;
        out += '<line x1="' + (ml + 8) + '" y1="' + (ly - 4) + '" x2="' + (ml + 24) + '" y2="' + (ly - 4) + '" stroke="' + COLORS[idx % COLORS.length] + '" stroke-width="2.4"/>';
        out += text(ml + 30, ly, "y = " + e.replace(/^\s*(?:y|f\(x\)|g\(x\)|h\(x\))\s*=\s*/i, ""), "start", 'font-size="11"');
      });
    }

    return figure(W, H, out, "Graph of y = " + exprs.join(" and y = "), 0, 0, 1.2);

  }


  /* pictures uploaded in the question form wait here under short names
     (up_xxxx); they are swapped for the real image when the question is saved */
  var uploads = {};
  var uploadCounter = 0;

  function svgImage(body) {

    var url = body.trim();

    if (/^up_[a-z0-9]+$/i.test(url)) {
      if (!uploads[url]) throw new Error("picture not found - upload it again");
      url = uploads[url];
    }

    if (!/^(https?:\/\/|data:image\/(png|jpe?g|gif|webp);base64,)/i.test(url)) {
      throw new Error("picture link must start with https://");
    }

    return '<span class="m-fig"><img class="m-img" alt="Question picture" loading="lazy" referrerpolicy="no-referrer" src="' + esc(url) + '"></span>';

  }


  function renderTag(name, body) {

    try {

      switch (name.toLowerCase()) {
        case "angle": return svgAngle(parseParams(body));
        case "triangle": return svgTriangle(parseParams(body));
        case "rect":
        case "rectangle": return svgRect(parseParams(body));
        case "circle": return svgCircle(parseParams(body));
        case "prism":
        case "box": return svgPrism(parseParams(body), false);
        case "cube": return svgPrism(parseParams(body), true);
        case "cylinder": return svgCylinder(parseParams(body));
        case "cone": return svgCone(parseParams(body));
        case "sphere": return svgSphere(parseParams(body));
        case "trapezoid":
        case "trapezium": return svgTrapezoid(parseParams(body));
        case "graph": return svgGraph(body);
        case "img":
        case "image":
        case "picture": return svgImage(body);
        default: return null;
      }

    } catch (err) {

      return '<span class="m-err">[' + esc(name) + ': ' + esc(err.message) + ']</span>';

    }

  }


  /* =======================================================
     TEXT FORMATTING
     ======================================================= */

  function replaceSqrt(s) {

    var guard = 0;

    for (;;) {

      var i = s.indexOf("sqrt(");
      if (i < 0 || ++guard > 50) break;

      var depth = 0, j = i + 4, end = -1;
      for (; j < s.length; j++) {
        if (s[j] === "(") depth++;
        else if (s[j] === ")") { depth--; if (depth === 0) { end = j; break; } }
      }

      if (end < 0) { s = s.slice(0, i) + "\u221a(" + s.slice(i + 5); continue; }

      s = s.slice(0, i) +
        '<span class="m-sqrt">\u221a<span class="m-rad">' + s.slice(i + 5, end) + '</span></span>' +
        s.slice(end + 1);

    }

    return s;

  }

  function frac(n, d) {
    return '<span class="m-frac"><span>' + n + '</span><span>' + d + '</span></span>';
  }

  function formatText(raw) {

    var s = esc(raw);

    /* stacked fractions {a/b}, innermost first. Markers (not HTML) are used so
       the "/" inside closing tags can never be mistaken for a fraction bar. */
    for (var n = 0; n < 10; n++) {
      var next = s.replace(/\{([^{}\uE010-\uE012]*?)\/([^{}\uE010-\uE012]*?)\}/g, "\uE010$1\uE011$2\uE012");
      if (next === s) break;
      s = next;
    }

    s = replaceSqrt(s);

    /* big operators */
    s = s.replace(/\bint\[([^\],]+),([^\]]+)\]/g, function (m, lo, hi) {
      return '<span class="m-int"><span class="m-int-sign">\u222b</span><span class="m-int-lim"><span>' + hi.trim() + '</span><span>' + lo.trim() + '</span></span></span>';
    });
    s = s.replace(/\bint\b(?=[\s(]|$)/g, '<span class="m-int"><span class="m-int-sign">\u222b</span></span>');

    s = s.replace(/\bsum\[([^\],]+),([^\]]+)\]/g, function (m, lo, hi) {
      return '<span class="m-sum"><span>' + hi.trim() + '</span><span class="m-sum-sign">\u03a3</span><span>' + lo.trim() + '</span></span>';
    });

    s = s.replace(/\blim\[([^\]]+)\]/g, function (m, sub) {
      return '<span class="m-sum m-lim"><span class="m-lim-word">lim</span><span>' + sub.trim() + '</span></span>';
    });

    /* derivatives: d/dx, dy/dx, d^2y/dx^2 */
    s = s.replace(/\bd(?:\^(\d))?([a-z]?)\/d([a-z])(?:\^(\d))?(?![a-z0-9])/g, function (m, p1, num, den, p2) {
      var top = "d" + (p1 ? "<sup>" + p1 + "</sup>" : "") + num;
      var bot = "d" + den + (p2 ? "<sup>" + p2 + "</sup>" : (p1 ? "<sup>" + p1 + "</sup>" : ""));
      return frac(top, bot);
    });

    /* superscripts / subscripts */
    s = s.replace(/\^\(([^()]+)\)/g, "<sup>$1</sup>");
    s = s.replace(/\^\s*([+\-]?\d+(?:\.\d+)?|[a-zA-Z])/g, "<sup>$1</sup>");
    s = s.replace(/_\(([^()]+)\)/g, "<sub>$1</sub>");
    s = s.replace(/_([a-zA-Z0-9])/g, "<sub>$1</sub>");

    /* symbols */
    s = s.replace(/(\d)\s?deg\b/g, "$1\u00b0")
         .replace(/\bpi\b/g, "\u03c0")
         .replace(/\btheta\b/g, "\u03b8")
         .replace(/\balpha\b/g, "\u03b1")
         .replace(/\bbeta\b/g, "\u03b2")
         .replace(/\bdelta\b/g, "\u03b4")
         .replace(/\b(?:infinity|inf)\b/g, "\u221e")
         .replace(/-&gt;/g, "\u2192")
         .replace(/&lt;=/g, "\u2264")
         .replace(/&gt;=/g, "\u2265")
         .replace(/!=/g, "\u2260")
         .replace(/\+-/g, "\u00b1")
         .replace(/ \* /g, " \u00b7 ");

    /* fraction markers -> HTML */
    s = s.replace(/\uE010/g, '<span class="m-frac"><span>')
         .replace(/\uE011/g, '</span><span>')
         .replace(/\uE012/g, '</span></span>');

    return s;

  }


  function formatMath(value) {

    var raw = String(value == null ? "" : value);
    var out = "";
    var last = 0;
    var re = /\[\[\s*([a-zA-Z]+)\s*:?\s*([\s\S]*?)\]\]/g;
    var m;

    while ((m = re.exec(raw)) !== null) {

      var html = renderTag(m[1], m[2]);

      if (html === null) continue;          /* unknown tag: leave as text */

      out += formatText(raw.slice(last, m.index)) + html;
      last = m.index + m[0].length;

    }

    return out + formatText(raw.slice(last));

  }

  window.formatMath = formatMath;


  /* =======================================================
     TEACHER TOOLBAR + LIVE PREVIEW (question form)
     ======================================================= */

  var FIELD_IDS = ["questionDirections", "questionText", "choiceA", "choiceB", "choiceC", "choiceD"];
  var lastField = "questionText";

  function insertAtCursor(text) {

    var field = document.getElementById(lastField) || document.getElementById("questionText");
    if (!field) return;

    var start = field.selectionStart == null ? field.value.length : field.selectionStart;
    var end = field.selectionEnd == null ? field.value.length : field.selectionEnd;

    field.value = field.value.slice(0, start) + text + field.value.slice(end);
    field.focus();
    field.selectionStart = field.selectionEnd = start + text.length;

    updatePreview();

  }

  function updatePreview() {

    var box = document.getElementById("mathPreview");
    if (!box) return;

    function val(id) { var e = document.getElementById(id); return e ? e.value.trim() : ""; }

    var html = "";

    if (val("questionDirections")) html += '<div class="mp-dir">' + formatMath(val("questionDirections")) + '</div>';
    if (val("questionText")) html += '<div class="mp-q">' + formatMath(val("questionText")) + '</div>';

    ["A", "B", "C", "D"].forEach(function (L) {
      var el = document.getElementById("choice" + L);
      var row = el && el.offsetParent !== null ? val("choice" + L) : "";
      if (row) html += '<div class="mp-c"><strong>' + L + '.</strong> ' + formatMath(row) + '</div>';
    });

    html = html || '<span class="mp-empty">Type a question to see how students will see it.</span>';

    if (html !== box.getAttribute("data-last")) {
      box.setAttribute("data-last", html);
      box.innerHTML = html;
    }

  }



  /* =======================================================
     UPLOADED PICTURES: pack (before saving) / unpack (when editing)
     ======================================================= */

  var DATA_IMG_TAG = /\[\[\s*(?:img|image|picture)\s*:?\s*(data:image\/[a-z+]+;base64,[A-Za-z0-9+\/=]+)\s*\]\]/gi;
  var UP_IMG_TAG = /\[\[\s*(?:img|image|picture)\s*:?\s*(up_[a-z0-9]+)\s*\]\]/gi;

  function packImages(str) {
    return String(str == null ? "" : str).replace(UP_IMG_TAG, function (all, id) {
      return uploads[id] ? "[[img: " + uploads[id] + "]]" : all;
    });
  }

  function unpackImages(str) {
    return String(str == null ? "" : str).replace(DATA_IMG_TAG, function (all, data) {
      var id = null;
      for (var k in uploads) if (uploads[k] === data) { id = k; break; }
      if (!id) { id = "up_" + (++uploadCounter).toString(36) + Date.now().toString(36).slice(-3); uploads[id] = data; }
      return "[[img: " + id + "]]";
    });
  }

  function plainQuestionText(str) {
    return String(str == null ? "" : str).replace(DATA_IMG_TAG, "[picture]");
  }

  window.packQuestionImages = packImages;
  window.unpackQuestionImages = unpackImages;
  window.plainQuestionText = plainQuestionText;

  function formFields() {
    return FIELD_IDS.map(function (id) { return document.getElementById(id); }).filter(Boolean);
  }

  function packForm() { formFields().forEach(function (f) { f.value = packImages(f.value); }); }
  function unpackForm() { formFields().forEach(function (f) { f.value = unpackImages(f.value); }); updatePreview(); }

  /* wrap the app's own save / edit so the textboxes stay short */
  function hookApp() {

    if (typeof window.saveQuestion === "function" && !window.saveQuestion.__math) {
      var origSave = window.saveQuestion;
      window.saveQuestion = function () {
        packForm();
        try { return origSave.apply(this, arguments); }
        finally { unpackForm(); }
      };
      window.saveQuestion.__math = true;
    }

    if (typeof window.editQuestion === "function" && !window.editQuestion.__math) {
      var origEdit = window.editQuestion;
      window.editQuestion = function () {
        var r = origEdit.apply(this, arguments);
        unpackForm();
        return r;
      };
      window.editQuestion.__math = true;
    }

  }

  window.addEventListener("load", hookApp);

  function note(msg, bad) {
    var el = document.getElementById("mathUploadNote");
    if (!el) return;
    el.textContent = msg;
    el.style.color = bad ? "#dc2626" : "#16a34a";
  }

  /* shrink a photo to a web-sized JPEG (about 90 KB) so exams stay fast */
  function compressImage(file, done, fail) {

    var url = URL.createObjectURL(file);
    var img = new Image();

    img.onerror = function () { URL.revokeObjectURL(url); fail("That picture format isn't supported. Please use JPG or PNG."); };

    img.onload = function () {

      URL.revokeObjectURL(url);

      var maxSide = 800, quality = 0.8, data = "";

      for (var attempt = 0; attempt < 8; attempt++) {

        var ratio = Math.min(1, maxSide / Math.max(img.width, img.height));
        var w = Math.max(1, Math.round(img.width * ratio));
        var h = Math.max(1, Math.round(img.height * ratio));

        var canvas = document.createElement("canvas");
        canvas.width = w; canvas.height = h;
        var ctx = canvas.getContext("2d");
        ctx.fillStyle = "#ffffff";
        ctx.fillRect(0, 0, w, h);
        ctx.drawImage(img, 0, 0, w, h);

        data = canvas.toDataURL("image/jpeg", quality);

        if (data.length <= 120000) break;

        if (quality > 0.5) quality -= 0.1; else maxSide = Math.round(maxSide * 0.8);

      }

      if (data.length > 400000) { fail("That picture is too large even after shrinking. Try a smaller one."); return; }

      done(data);

    };

    img.src = url;

  }

  function handleUpload(file) {

    if (!file) return;

    if (!/^image\//i.test(file.type)) { note("Please choose an image file.", true); return; }

    note("Processing picture...");

    compressImage(file, function (data) {
      var id = "up_" + (++uploadCounter).toString(36) + Date.now().toString(36).slice(-3);
      uploads[id] = data;
      insertAtCursor("[[img: " + id + "]]");
      note("Picture added (" + Math.round(data.length * 0.75 / 1024) + " KB).");
    }, function (msg) { note(msg, true); });

  }

  function initToolbar() {

    var bar = document.getElementById("mathToolbar");
    if (!bar) return;

    bar.addEventListener("mousedown", function (e) {
      if (e.target.closest("button")) e.preventDefault();      /* keep the cursor in the text box */
    });

    bar.addEventListener("click", function (e) {

      var up = e.target.closest("button[data-action=upload]");
      if (up) {
        var input = document.getElementById("mathImageInput");
        if (input) input.click();
        return;
      }

      var btn = e.target.closest("button[data-insert]");
      if (btn) insertAtCursor(btn.getAttribute("data-insert"));

    });

    var fileInput = document.getElementById("mathImageInput");
    if (fileInput) {
      fileInput.addEventListener("change", function () {
        handleUpload(fileInput.files && fileInput.files[0]);
        fileInput.value = "";
      });
    }

    document.addEventListener("focusin", function (e) {
      if (e.target && FIELD_IDS.indexOf(e.target.id) >= 0) lastField = e.target.id;
    });

    FIELD_IDS.forEach(function (id) {
      var el = document.getElementById(id);
      if (el) el.addEventListener("input", updatePreview);
    });

    var typeSelect = document.getElementById("questionType");
    if (typeSelect) typeSelect.addEventListener("change", function () { setTimeout(updatePreview, 0); });

    updatePreview();
    setInterval(updatePreview, 1500);      /* also catches Edit / Clear buttons */

  }

  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", initToolbar);
  else initToolbar();

})();
