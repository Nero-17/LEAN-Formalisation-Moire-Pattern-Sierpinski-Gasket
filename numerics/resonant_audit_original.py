"""Independent integer-coordinate reconstruction for a manuscript review."""
import math
from pathlib import Path
from collections import deque

def cross(a,b,c):
    return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])

def hull(points):
    points=sorted(set(points)); out=[]
    for seq in [points,points[::-1]]:
        half=[]
        for x in seq:
            while len(half)>1 and cross(half[-2],half[-1],x)<=0: half.pop()
            half.append(x)
        out+=half[:-1]
    return out

def compute(m,n):
    q=m*m-m*n+n*n
    a=m*m-2*m*n; b=n*n-2*m*n
    p=[(1,0),(0,1),(-1,-1)]
    r=[(a*x-b*y,b*x+(a-b)*y) for x,y in p]
    digits=[[(q*x-u,q*y-v) for u,v in r] for x,y in p]
    polygon=hull([(-x,-y) for ds in digits for x,y in ds])
    edges=list(zip(polygon,polygon[1:]+polygon[:1]))
    def live(c): return all(cross(u,v,c)>=0 for u,v in edges)
    states=[frozenset([(0,0)])]; index={states[0]:0}; transitions=[]
    for state in states:
        row=[]
        for ds in digits:
            target=frozenset((2*x+u,2*y+v) for x,y in state for u,v in ds if live((2*x+u,2*y+v)))
            if target:
                if target not in index:
                    index[target]=len(states); states.append(target)
                row.append(index[target])
        transitions.append(row)
        if len(states)>200000: raise RuntimeError('state cap')
    # Tarjan components avoid zero-dimensional terminal states spoiling lower bounds.
    counter=[0]; indices={}; lows={}; stack=[]; active=set(); components=[]
    def visit(v):
        indices[v]=lows[v]=counter[0]; counter[0]+=1
        stack.append(v); active.add(v)
        for w in transitions[v]:
            if w not in indices: visit(w); lows[v]=min(lows[v],lows[w])
            elif w in active: lows[v]=min(lows[v],indices[w])
        if lows[v]==indices[v]:
            part=[]
            while True:
                w=stack.pop(); active.remove(w); part.append(w)
                if w==v: break
            components.append(part)
    for v in range(len(states)):
        if v not in indices: visit(v)
    bounds=[]
    for part in components:
        local={v:i for i,v in enumerate(part)}
        rows=[[local[w] for w in transitions[v] if w in local] for v in part]
        vector=[1.]*len(part)
        for step in range(10000):
            out=[vector[i]+sum(vector[j] for j in row) for i,row in enumerate(rows)]
            ratios=[out[i]/vector[i] for i in range(len(part))]
            low=min(ratios)-1; high=max(ratios)-1
            norm=max(out); vector=[x/norm for x in out]
            if high-low<1e-11:break
        bounds.append((low,high))
    low=max(x[0] for x in bounds); high=max(x[1] for x in bounds)
    return dict(m=m,n=n,N=q,states=len(states),steps=step,
        dim_lower=math.log2(low),dim_upper=math.log2(high),
        theta=math.degrees(abs(math.atan2(b*math.sqrt(3)/2,a-b/2))))

if __name__=='__main__':
    for pair in [(1,0),(1,-1),(3,1),(4,1),(5,1),(5,2),(7,1)]:
        print(compute(*pair),flush=True)
