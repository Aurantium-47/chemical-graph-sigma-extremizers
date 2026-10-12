"""Exact finite checks for extremal chemical-graph degree multiplicities."""
from pathlib import Path
import json, sys, time, hashlib
from itertools import combinations

OUT = Path(__file__).resolve().parent
SCALE = 1 << 48

def expected(n):
    q, r = divmod(n, 4)
    return [
        [(q,q,q,q)],
        [(q,q,q,q+1)],
        [(q,q+1,q,q+1),(q+1,q,q+1,q)],
        [(q+1,q,q+1,q+1)],
    ][r]

def nth_root_bounds(base, n):
    target = base * SCALE**n
    lo, hi = SCALE, 2*SCALE
    while hi-lo > 1:
        mid=(hi+lo)//2
        if mid**n <= target:
            lo=mid
        else:
            hi=mid
    assert lo**n < target < hi**n
    return lo, hi

def counts(a):
    # Independently aggregate six degree-class pairs by absolute degree difference.
    out=[0,0,0]
    for i,j in combinations(range(4),2):
        out[j-i-1] += a[i]*a[j]
    return tuple(out)

def diff_lower(x, y, t, s):
    delta = [p-q for p,q in zip(x,y)]
    return (delta[0]*SCALE
        +delta[1]*t[delta[1]<0]
        +delta[2]*s[delta[2]<0])

def enumerate_integer_vectors():
    records=[]
    for n in range(7,61):
        win=set(expected(n))
        cw=counts(next(iter(win)))
        assert len({counts(a) for a in win})==1
        t,s=nth_root_bounds(2,n),nth_root_bounds(3,n)
        seen=set()
        total=0
        min_num=None
        for a in range(n+1):
            for b in range(n-a+1):
                for c in range(n-a-b+1):
                    if (a+c)%2:
                        continue
                    v=(a,b,c,n-a-b-c)
                    total+=1
                    cv=counts(v)
                    if cv==cw:
                        seen.add(v)
                    else:
                        lower=diff_lower(cw,cv,t,s)
                        assert lower>0,(n,v,lower)
                        min_num=lower if min_num is None else min(min_num,lower)
        assert seen==win
        records.append(dict(n=n,vectors=total,winners=sorted(win),
                            min_certified_difference_numerator=min_num,
                            difference_denominator=SCALE,
                            root_bounds={"2":t,"3":s}))
    return records

def erdos_gallai(ds):
    ds=sorted(ds,reverse=True)
    if sum(ds)%2:
        return False
    return all(sum(ds[:k])<=k*(k-1)+sum(min(k,d) for d in ds[k:])
               for k in range(1,len(ds)+1))

def graphicality_boundary_check():
    results=[]
    for n in (7,8,9):
        tested=0
        failures=[]
        for a in range(n+1):
            for b in range(n-a+1):
                for c in range(n-a-b+1):
                    d=n-a-b-c
                    if (a+c)%2:
                        continue
                    tested+=1
                    ds=[1]*a+[2]*b+[3]*c+[4]*d
                    if not erdos_gallai(ds):
                        failures.append([a,b,c,d])
        if n>=8:
            assert not failures
        results.append(dict(n=n,vectors=tested,nongraphical_vectors=failures))
    return results

def hh(ds):
    remaining={i:d for i,d in enumerate(ds)}
    adj=[set() for _ in ds]
    while remaining:
        u=max(remaining,key=lambda v:(remaining[v],v))
        d=remaining.pop(u)
        others=sorted(remaining,key=lambda v:(remaining[v],v),reverse=True)[:d]
        assert len(others)==d and all(remaining[v]>0 for v in others)
        for v in others:
            adj[u].add(v)
            adj[v].add(u)
            remaining[v]-=1
    assert [len(x) for x in adj]==ds
    return adj

def component(adj, start):
    seen={start}
    stack=[start]
    while stack:
        u=stack.pop()
        for v in adj[u]-seen:
            seen.add(v)
            stack.append(v)
    return seen

def components(adj):
    unseen=set(range(len(adj)))
    result=[]
    while unseen:
        c=component(adj,min(unseen))
        result.append(c)
        unseen-=c
    return result

def edges(adj):
    return [[u,v] for u in range(len(adj)) for v in sorted(adj[u]) if u<v]

def connected_realizations():
    records=[]
    for n in range(7,201):
        for mult in expected(n):
            ds=[d for d,c in enumerate(mult,1) for _ in range(c)]
            adj=hh(ds)
            before=len(components(adj))
            switches=[]
            while len(components(adj))>1:
                comps=components(adj)
                cyc=next(c for c in comps if sum(len(adj[u]) for u in c)//2>=len(c))
                chosen=None
                for u in sorted(cyc):
                    for v in sorted(adj[u]):
                        if u>=v:
                            continue
                        adj[u].remove(v)
                        adj[v].remove(u)
                        intact=component(adj,u)==cyc
                        adj[u].add(v)
                        adj[v].add(u)
                        if intact:
                            chosen=(u,v)
                            break
                    if chosen:
                        break
                assert chosen is not None
                u,v=chosen
                other=next(c for c in comps if c!=cyc)
                x=min(other)
                y=min(adj[x])
                assert x not in adj[u] and y not in adj[v]
                for p,q in ((u,v),(x,y)):
                    adj[p].remove(q)
                    adj[q].remove(p)
                for p,q in ((u,x),(v,y)):
                    adj[p].add(q)
                    adj[q].add(p)
                assert [len(a) for a in adj]==ds
                assert len(components(adj))==len(comps)-1
                switches.append(dict(removed=[[u,v],[x,y]],added=[[u,x],[v,y]]))
            e=edges(adj)
            assert len(e)==sum(ds)//2
            assert len(component(adj,0))==n and all(u!=v for u,v in e)
            records.append(dict(n=n,multiplicities=mult,degrees=ds,
                                initial_component_count=before,switches=switches,edges=e))
    return records

def verify_original_n7():
    e=[(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,6),(2,3)]
    assert len(set(e))==len(e)
    adj=[set() for _ in range(7)]
    for u,v in e:
        assert u!=v
        adj[u].add(v)
        adj[v].add(u)
    ds=[len(a) for a in adj]
    assert ds==[4,4,3,3,2,1,1] and len(component(adj,0))==7
    return dict(edges=e,degrees=ds,connected=True,simple=True)

def main():
    start=time.time()
    enum=enumerate_integer_vectors()
    boundary=graphicality_boundary_check()
    graphs=connected_realizations()
    n7=verify_original_n7()
    graph_path=OUT/"connected_graphs.json"
    graph_path.write_text(json.dumps(graphs,indent=2),encoding="utf-8")
    summary=dict(
        python=sys.version, dependency="Python standard library only",
        integer_enumeration_range=[7,60],
        total_vectors=sum(r["vectors"] for r in enum),
        min_gap_record=min(enum,key=lambda r:r["min_certified_difference_numerator"]),
        n_values=len(enum),
        graphicality_boundary=boundary,
        candidate_graphs=len(graphs),
        graph_n_range=[7,200],
        graphs_requiring_switch=sum(bool(r["switches"]) for r in graphs),
        total_switches=sum(len(r["switches"]) for r in graphs),
        original_n7=n7,
        graph_certificate_file=graph_path.name,
        graph_certificate_sha256=hashlib.sha256(graph_path.read_bytes()).hexdigest(),
        passed=True,
        seconds=time.time()-start)
    (OUT/"verification.json").write_text(
        json.dumps(dict(summary=summary,enumeration=enum),indent=2),encoding="utf-8")
    print(json.dumps(summary,indent=2))

if __name__=="__main__":
    main()

