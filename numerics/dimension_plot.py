"""Plot resonant dimensions and non-resonant fits; requires NumPy/Matplotlib."""
from pathlib import Path
import csv
import math
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

root = Path(__file__).resolve().parents[1]
data = np.loadtxt(root / 'data/mtheta_data.dat', skiprows=1)
with (root / 'numerics/survivor_counts.csv').open() as stream:
    counts = list(csv.DictReader(stream))
angles = [
    ('pi/4', math.pi/4, r'$\pi/4$', (62, 1.191)),
    ('pi/6', math.pi/6, r'$\pi/6$', (30, 1.142)),
    ('pi/12', math.pi/12, r'$\pi/12$', (15, 1.202)),
    ('atan(sqrt(3)/2)', math.atan(math.sqrt(3)/2),
     r'$\arctan(\sqrt{3}/2)$', (55, 1.211)),
]
fits = []
for key, theta, label, pos in angles:
    for lo, hi in [(8,12), (12,20), (14,20), (16,20), (18,20)]:
        rows = sorted((r for r in counts if r['angle'] == key and lo <= int(r['depth']) <= hi),
                      key=lambda r: int(r['depth']))
        assert len(rows) == hi-lo+1
        slope = np.polyfit([int(r['depth']) for r in rows],
                           np.log2([int(r['count']) for r in rows]), 1)[0]
        fits.append(dict(angle=key, start=lo, end=hi, slope=float(slope)))
with (root / 'numerics/growth_fits.csv').open('w', newline='') as stream:
    writer = csv.DictWriter(stream, fieldnames=fits[0].keys())
    writer.writeheader()
    writer.writerows(fits)

plt.rcParams.update({'font.family':'DejaVu Sans', 'font.size':10,
                     'mathtext.fontset':'stix', 'pdf.fonttype':42,
                     'axes.spines.top':False, 'axes.spines.right':False})
fig, ax = plt.subplots(figsize=(7.1,3.9), layout='constrained')
ax.scatter(data[:,0], data[:,1], s=12, c='#2466B4', alpha=.8, linewidths=0,
           label='Resonant angles', zorder=3)
ax.axhline(math.log2(9/4), c='#C93337', ls=(0,(6,4)), lw=1.3,
           label=r'$2\dim_{\mathrm{H}}(S)-2=\log_2(9/4)\approx1.169925$', zorder=2)
for key, theta, label, pos in angles:
    slope = next(r['slope'] for r in fits if r['angle']==key and r['start']==16)
    ax.scatter(math.degrees(theta), slope, s=43, c='#D92D39',
               edgecolors='white', linewidths=.7,
               label='Non-resonant estimates' if key=='pi/4' else None, zorder=5)
    ax.annotate(label, xy=(math.degrees(theta),slope), xytext=pos,
                ha='center', va='center', color='#B5222C',
                arrowprops={'arrowstyle':'-', 'lw':.65, 'color':'#C35B60'},
                bbox={'facecolor':'white','edgecolor':'none','alpha':.9,'pad':1}, zorder=6)
ax.set(xlim=(-3,123), ylim=(1.125,1.225), xlabel=r'$\theta\ ({}^\circ)$')
ax.set_xticks(np.arange(0,121,20))
ax.set_yticks(np.arange(1.125,1.226,.025))
handles, labels = ax.get_legend_handles_labels()
ax.legend([handles[i] for i in (0,2,1)], [labels[i] for i in (0,2,1)],
          loc='upper right', fontsize=8, frameon=False, handletextpad=.5)
ax.grid(color='#E4E8ED', lw=.6, zorder=0)
(root/'figures').mkdir(exist_ok=True)
fig.savefig(root/'figures/dimensions-comparison.pdf')
fig.savefig(root/'figures/dimensions-comparison.png', dpi=180)
