"""Generate SVG plot of the bimodal total domination polynomials for the
22,601-vertex and 25,423-vertex connected bipartite counterexamples to
Alikhani-Jafari (2016) Conjecture 2.9, directly from exact FLINT polynomials.
"""
from pathlib import Path

from flint import fmpz_poly as Poly
import graph_exact

OUT_PATH = Path(__file__).resolve().parent.parent / "paper" / "valley_plot.svg"


def extract_profile(m, p, w, d, Q, k_min, k_max):
    qs = graph_exact.sizes(m, Q)
    _, nv, c = graph_exact.graph(m, p, w, d, qs)
    n = nv + c + 2
    H = graph_exact.from_right(m, p, w, d, qs)
    X = Poly([0, 1])
    full = H * X * (1 + X) ** (c + 1)
    raw = [int(full[k]) for k in range(k_min, k_max + 1)]
    peaks = [
        k for k in range(k_min + 1, k_max)
        if int(full[k - 1]) < int(full[k]) > int(full[k + 1])
    ]
    p1, p2 = peaks[0], peaks[-1]
    valley_k = min(range(p1, p2 + 1), key=lambda k: int(full[k]))
    v_val = int(full[valley_k])
    scale = 1 << (v_val.bit_length() - 60)
    v_s = v_val // scale
    ratios = [(val // scale) / v_s for val in raw]
    return {
        "n": n,
        "edges": sum(map(len, graph_exact.graph(m, p, w, d, qs)[0])) // 2,
        "m": m, "p": p, "w": w, "d": d, "Q": Q,
        "k_min": k_min, "k_max": k_max,
        "peaks": peaks, "valley": valley_k,
        "left_ratio": (int(full[p1]) // scale) / v_s,
        "right_ratio": (int(full[p2]) // scale) / v_s,
        "ratios": ratios,
    }


def make_svg(prof1, prof2, out_path):
    W, H = 840, 330
    panels = [
        (prof1, 62, 398, "A. 22,601-vertex graph (m=156, p=2, w=9, d=2, Q=969)"),
        (prof2, 474, 814, "B. 25,423-vertex graph (m=117, p=3, w=6, d=2, Q=1090)"),
    ]
    top_y, bot_y = 48, 272

    lines = [
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" width="{W}" height="{H}">',
        '<defs><style>',
        '  .title { font-family: "Helvetica Neue", Helvetica, Arial, sans-serif; font-size: 11.5px; font-weight: 600; fill: #1a1a2e; }',
        '  .axis-label { font-family: "Helvetica Neue", Helvetica, Arial, sans-serif; font-size: 10.5px; fill: #333; }',
        '  .tick { font-family: "Helvetica Neue", Helvetica, Arial, sans-serif; font-size: 9.5px; fill: #555; }',
        '  .annot { font-family: "Helvetica Neue", Helvetica, Arial, sans-serif; font-size: 9.2px; font-weight: 600; }',
        '  .grid { stroke: #e5e7eb; stroke-width: 0.8; stroke-dasharray: 2,2; }',
        '  .axis { stroke: #374151; stroke-width: 1.1; fill: none; }',
        '</style></defs>',
        f'<rect width="{W}" height="{H}" fill="#ffffff"/>',
    ]

    for prof, x0, x1, title in panels:
        k_min, k_max = prof["k_min"], prof["k_max"]
        ratios = prof["ratios"]
        y_min = min(ratios)
        y_max = max(ratios)
        pad = (y_max - y_min) * 0.14
        ymin_plot = y_min - pad * 0.5
        ymax_plot = y_max + pad * 1.15

        def sx(k):
            return x0 + (k - k_min) / (k_max - k_min) * (x1 - x0)

        def sy(r):
            return bot_y - (r - ymin_plot) / (ymax_plot - ymin_plot) * (bot_y - top_y)

        lines.append(f'<text x="{(x0+x1)/2:.1f}" y="24" text-anchor="middle" class="title">{title}</text>')

        for t_i in range(5):
            rv = ymin_plot + (ymax_plot - ymin_plot) * t_i / 4
            yy = sy(rv)
            lines.append(f'<line x1="{x0}" y1="{yy:.1f}" x2="{x1}" y2="{yy:.1f}" class="grid"/>')
            lines.append(f'<text x="{x0-6}" y="{yy+3.2:.1f}" text-anchor="end" class="tick">{rv:.4f}</text>')

        y1 = sy(1.0)
        lines.append(
            f'<line x1="{x0}" y1="{y1:.1f}" x2="{x1}" y2="{y1:.1f}" '
            'stroke="#dc2626" stroke-width="0.9" stroke-dasharray="4,3" opacity="0.7"/>'
        )

        step = 20 if (k_max - k_min) <= 100 else 40
        first_tick = ((k_min + step - 1) // step) * step
        for kv in range(first_tick, k_max + 1, step):
            xx = sx(kv)
            lines.append(f'<line x1="{xx:.1f}" y1="{top_y}" x2="{xx:.1f}" y2="{bot_y}" class="grid"/>')
            lines.append(f'<text x="{xx:.1f}" y="{bot_y+14}" text-anchor="middle" class="tick">{kv:,}</text>')

        p1, p2, vk = prof["peaks"][0], prof["peaks"][-1], prof["valley"]
        pts = [f"{sx(k_min + idx):.2f},{sy(r):.2f}" for idx, r in enumerate(ratios)]
        fill_pts = f"{x0:.2f},{bot_y:.2f} " + " ".join(pts) + f" {x1:.2f},{bot_y:.2f}"
        lines.append(f'<polygon points="{fill_pts}" fill="#2563eb" opacity="0.08"/>')
        lines.append(f'<polyline points="{" ".join(pts)}" fill="none" stroke="#1d4ed8" stroke-width="2.1"/>')

        xp1, yp1 = sx(p1), sy(ratios[p1 - k_min])
        xv, yv = sx(vk), sy(ratios[vk - k_min])
        xp2, yp2 = sx(p2), sy(ratios[p2 - k_min])

        lines.append(f'<circle cx="{xp1:.2f}" cy="{yp1:.2f}" r="3.6" fill="#059669" stroke="#fff" stroke-width="1"/>')
        lines.append(f'<circle cx="{xv:.2f}" cy="{yv:.2f}" r="3.8" fill="#dc2626" stroke="#fff" stroke-width="1"/>')
        lines.append(f'<circle cx="{xp2:.2f}" cy="{yp2:.2f}" r="3.6" fill="#059669" stroke="#fff" stroke-width="1"/>')

        lines.append(f'<text x="{xp1-4:.1f}" y="{yp1-8:.1f}" text-anchor="middle" class="annot" fill="#047857">Peak 1 ({p1:,})</text>')
        lines.append(f'<text x="{xp2+4:.1f}" y="{yp2-8:.1f}" text-anchor="middle" class="annot" fill="#047857">Peak 2 ({p2:,})</text>')
        lines.append(f'<text x="{xv:.1f}" y="{yv+15:.1f}" text-anchor="middle" class="annot" fill="#b91c1c">Valley ({vk:,})</text>')

        lines.append(f'<rect x="{x0}" y="{top_y}" width="{x1-x0}" height="{bot_y-top_y}" class="axis"/>')
        lines.append(
            f'<text x="{(x0+x1)/2:.1f}" y="{bot_y+34}" text-anchor="middle" class="axis-label">'
            'Total dominating set cardinality <tspan font-style="italic">k</tspan></text>'
        )

    ymid = (top_y + bot_y) / 2
    lines.append(
        f'<text x="15" y="{ymid:.1f}" text-anchor="middle" transform="rotate(-90 15 {ymid:.1f})" class="axis-label">'
        'Normalized count  '
        '<tspan font-style="italic">d</tspan><tspan dy="2.6" font-size="7.6px" font-style="italic">t</tspan><tspan dy="-2.6">(<tspan font-style="italic">G</tspan>, <tspan font-style="italic">k</tspan>) / </tspan>'
        '<tspan font-style="italic">d</tspan><tspan dy="2.6" font-size="7.6px" font-style="italic">t</tspan><tspan dy="-2.6">(<tspan font-style="italic">G</tspan>, <tspan font-style="italic">k</tspan></tspan><tspan dy="2.6" font-size="7.6px">2</tspan><tspan dy="-2.6">)</tspan>'
        '</text>'
    )
    lines.append('</svg>')
    out_path.write_text("\n".join(lines))
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    p1 = extract_profile(156, 2, 9, 2, 969, 11815, 11915)
    p2 = extract_profile(117, 3, 6, 2, 1090, 13260, 13415)
    make_svg(p1, p2, OUT_PATH)
