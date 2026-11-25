"""Schematic of one clause gadget of the ring-clause graph G(m,p,q) (w=3, d=1), drawn with p=2."""
W, H = 660, 320
hub, leaf = (360, 30), (470, 30)
yv, yc = 140, 240
A = {}
xs = {2: 70, 1: 185, 0: 300}            # block i-s
for s, x0 in xs.items():
    for a in range(2):
        A[(s, a)] = (x0 + 50 * a, yv)
Bv, Zv = (470, yv), (600, yv)
cl = []                                 # clause vertices (position, neighbour)
cx = 50
for s in (2, 1, 0):
    for a in range(2):
        cl.append(((cx, yc), A[(s, a)], f"c<tspan font-size='9' dy='3'>i,b,{s},{a}</tspan>"))
        cx += 58
zpos = (560, yc)
out = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" width="{W}" height="{H}">',
       '<rect width="100%" height="100%" fill="white"/>',
       '<style>text{font-family:"New Computer Modern","Latin Modern Roman",serif;font-size:14px;fill:#111}'
       '.it{font-style:italic}.sm{font-size:11px;fill:#444}</style>']
def box(x0, x1, text):
    out.append(f'<rect x="{x0}" y="{yv-38}" width="{x1-x0}" height="56" rx="8" fill="#eef2ff" stroke="#c7d2fe"/>')
    out.append(f'<text x="{(x0+x1)/2}" y="{yv+32}" text-anchor="middle" class="sm">{text}</text>')
for s_, x0 in xs.items():
    box(x0 - 24, x0 + 74, "block i" if s_ == 0 else f"block i−{s_}")
box(Bv[0] - 30, Zv[0] + 30, "block i (one of q pairs)")
def line(p, q, col="#222", w=1.2, dash=None):
    d = f' stroke-dasharray="{dash}"' if dash else ""
    out.append(f'<line x1="{p[0]}" y1="{p[1]}" x2="{q[0]}" y2="{q[1]}" stroke="{col}" stroke-width="{w}"{d}/>')
# hub edges to variables (light)
for v in list(A.values()) + [Bv, Zv]:
    line(hub, v, "#9aa5b1", 0.9)
line(hub, leaf, "#222", 1.4)
for pos, nb, _ in cl:
    line(pos, Bv, "#c2410c", 0.9); line(pos, nb, "#c2410c", 0.9)
line(zpos, Bv, "#c2410c", 0.9); line(zpos, Zv, "#c2410c", 0.9)
def dot(p, fill, r=6.5, stroke="#111"):
    out.append(f'<circle cx="{p[0]}" cy="{p[1]}" r="{r}" fill="{fill}" stroke="{stroke}" stroke-width="1.2"/>')
def label(p, txt, dx=0, dy=0, anchor="middle", cls="it"):
    out.append(f'<text x="{p[0]+dx}" y="{p[1]+dy}" text-anchor="{anchor}" class="{cls}">{txt}</text>')
dot(hub, "#111"); label(hub, "h", -14, 5)
dot(leaf, "white"); label(leaf, "ℓ", 14, 5)
for (s, a), p in A.items():
    dot(p, "#2563eb")
    sub = "i" if s == 0 else f"i−{s}"
    label(p, f"A<tspan font-size='9' dy='3'>{sub},{a}</tspan>", 0, -14)
dot(Bv, "#2563eb"); label(Bv, "B<tspan font-size='9' dy='3'>i,b</tspan>", 0, -14)
dot(Zv, "#2563eb"); label(Zv, "Z<tspan font-size='9' dy='3'>i,b</tspan>", 0, -14)
for pos, _, txt in cl:
    dot(pos, "white", 5); label(pos, txt, 0, 22)
dot(zpos, "white", 5); label(zpos, "z<tspan font-size='9' dy='3'>i,b</tspan>", 0, 22)
label((20, 308), "blue: variable vertices (all adjacent to h, grey edges);  white: free vertices ℓ, z, c (clause edges orange)", 0, 0, "start", "sm")
out.append('</svg>')
open("construction.svg", "w").write("\n".join(out))
print("wrote construction.svg")
