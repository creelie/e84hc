"""place.py -- label placement that cannot collide with the drawing.

The renderer emits every path as an explicit list of projected coordinates, so
the ink of a figure is known exactly once the geometry has been emitted.  This
module reads those coordinates back, forms the ink rectangle, and then places
each label OUTSIDE that rectangle, on the side nearest its anchor, stacked so
that no two labels touch.  A thin leader joins the label to its anchor.

Nothing is placed by hand and nothing is placed on top of the drawing, so the
two failure modes of a hand-placed label, sitting on a curve and sitting on
another label, are both excluded by construction rather than by inspection.
"""
import re

COORD = re.compile(r'\(\s*(-?\d+\.?\d*)\s*,\s*(-?\d+\.?\d*)\s*\)')


def ink_box(body):
    xs, ys = [], []
    for mx, my in COORD.findall(body):
        xs.append(float(mx))
        ys.append(float(my))
    if not xs:
        raise ValueError("no geometry emitted")
    return min(xs), min(ys), max(xs), max(ys)


class Placer:
    """Collects (anchor, text, style) and lays the labels out around the ink."""

    def __init__(self, gap=0.24, pitch=0.50, char=0.150, height=0.32):
        self.items = []
        self.gap = gap          # clear space between ink and label box
        self.pitch = pitch      # vertical pitch between stacked labels
        self.char = char        # width per character, in cm
        self.height = height

    def add(self, anchor, text, style="", side=None, width=None):
        self.items.append(dict(anchor=anchor, text=text, style=style,
                               side=side, width=width))

    # ------------------------------------------------------------------
    def _width(self, it):
        if it["width"] is not None:
            return it["width"]
        return self.char * max(3.0, len(_plain(it["text"])))

    def emit(self, body, cam):
        x0, y0, x1, y1 = ink_box(body)
        cx = 0.5 * (x0 + x1)
        for it in self.items:
            (ax, ay), _ = cam.project(it["anchor"])
            it["ax"], it["ay"] = ax, ay
            if it["side"] is None:
                it["side"] = "L" if ax < cx else "R"

        out = []
        for side in ("L", "R"):
            group = [it for it in self.items if it["side"] == side]
            group.sort(key=lambda it: -it["ay"])
            # stack from the anchor heights, then push apart to the pitch
            ys = [it["ay"] for it in group]
            for i in range(1, len(ys)):
                if ys[i - 1] - ys[i] < self.pitch:
                    ys[i] = ys[i - 1] - self.pitch
            # recentre the stack on the anchors it came from
            if ys:
                shift = (sum(it["ay"] for it in group) - sum(ys)) / len(ys)
                ys = [y + shift for y in ys]
            for it, y in zip(group, ys):
                w = self._width(it)
                if side == "L":
                    xt = x0 - self.gap - w / 2.0
                    edge = xt + w / 2.0
                else:
                    xt = x1 + self.gap + w / 2.0
                    edge = xt - w / 2.0
                out.append("  \\draw[PRule,line width=0.35pt] "
                           "(%.4f,%.4f) -- (%.4f,%.4f);\n"
                           % (edge, y, it["ax"], it["ay"]))
                out.append("  \\node[%sanchor=%s,inner sep=0pt] at (%.4f,%.4f) "
                           "{%s};\n"
                           % ((it["style"] + ",") if it["style"] else "",
                              "east" if side == "L" else "west",
                              edge + (-0.10 if side == "L" else 0.10), y,
                              it["text"]))
        return "".join(out)

    def check(self, body, cam):
        """Assert that no label box meets the ink box or another label box."""
        x0, y0, x1, y1 = ink_box(body)
        boxes = []
        for side in ("L", "R"):
            pass
        # recompute the same layout, then test
        placed = self.emit(body, cam)
        nodes = re.findall(r'anchor=(east|west),inner sep=0pt\] at '
                           r'\((-?\d+\.?\d*),(-?\d+\.?\d*)\)', placed)
        for it, (anc, sx, sy) in zip(
                sorted(self.items, key=lambda i: (i["side"], -i["ay"])), nodes):
            w = self._width(it)
            x = float(sx)
            lo = x - w if anc == "east" else x
            hi = x if anc == "east" else x + w
            boxes.append((lo, float(sy) - self.height / 2,
                          hi, float(sy) + self.height / 2, it["text"]))
        bad = []
        for i, a in enumerate(boxes):
            if a[0] < x1 and x0 < a[2] and a[1] < y1 and y0 < a[3]:
                bad.append(("ink", a[4]))
            for b in boxes[i + 1:]:
                if a[0] < b[2] and b[0] < a[2] and a[1] < b[3] and b[1] < a[3]:
                    bad.append((a[4], b[4]))
        return bad


def _plain(s):
    out, skip = [], False
    for ch in s:
        if ch == "\\":
            skip = True
            continue
        if skip and not ch.isalpha():
            skip = False
        if skip:
            continue
        if ch not in "${}^_":
            out.append(ch)
    return "".join(out)
