#!/usr/bin/env python3
"""checkfigs.py -- assert that no two labels overlap in any figure.

A label box is estimated from its text: the width from the longest line, so
that a multi-line node is not counted as one long line, and the axes swapped
for a node carrying rotate=90, so that a vertical label is not counted as a
horizontal one.  Nodes with no printable text are dots and are skipped.
A small pad is added on every side, so labels that merely touch also fail.
"""
import re, glob, sys
sys.path.insert(0, '.')
from place import _plain

NODE = re.compile(r'\\node\[([^\]]*)\]\s*at\s*\((-?[\d.]+),\s*(-?[\d.]+)\)\s*\{(.*?)\};', re.S)
CH, LH, PAD = 0.155, 0.32, 0.03


def box(spec, x, y, text):
    lines = [_plain(t) for t in re.split(r'\\\\', text)]
    lines = [l for l in lines if l.strip()] or ['']
    w = CH * max(2.0, max(len(l) for l in lines))
    h = LH * len(lines)
    if 'rotate=90' in spec or 'rotate=-90' in spec:
        w, h = h, w
    if 'anchor=east' in spec:    lo, hi = x - w, x
    elif 'anchor=west' in spec:  lo, hi = x, x + w
    else:                        lo, hi = x - w / 2, x + w / 2
    if 'anchor=north' in spec:   b, t = y - h, y
    elif 'anchor=south' in spec: b, t = y, y + h
    else:                        b, t = y - h / 2, y + h / 2
    return (lo - PAD, b - PAD, hi + PAD, t + PAD,
            ' '.join(text.split())[:34])


def main():
    total = 0
    for fn in sorted(glob.glob('fig_*.tex')):
        boxes = []
        for spec, x, y, txt in NODE.findall(open(fn).read()):
            if _plain(txt).strip():
                boxes.append(box(spec, float(x), float(y), txt))
        hits = [(a[4], b[4]) for i, a in enumerate(boxes) for b in boxes[i+1:]
                if a[0] < b[2] and b[0] < a[2] and a[1] < b[3] and b[1] < a[3]]
        total += len(hits)
        print("  [%s] %-22s %d labels%s"
              % ("FAIL" if hits else "PASS", fn, len(boxes),
                 ("   " + str(hits[:2])) if hits else ""))
    print()
    print("  overlapping label pairs across all figures: %d" % total)
    return 0 if total == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
