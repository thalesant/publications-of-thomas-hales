#!/usr/bin/env python3
"""Independent exact checks of selected paper identities and numerical margins.
Requires SymPy, but is not imported by the OCaml controller. This is not a
Wolfram execution, a validation of the interval backend, or a full proof run.
Algebraic signs use outward rational intervals; no floating sign decision.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,json,math
import sympy as S
from sympy.parsing.mathematica import parse_mathematica
ROOT=Path(__file__).resolve().parents[1]
BITS=192; SCALE=1<<BITS

def interval(a,b=None):
    a=F(a);b=a if b is None else F(b)
    if a>b:raise ValueError('unordered interval')
    return a,b

def add(a,b):return a[0]+b[0],a[1]+b[1]
def mul(a,b):
    v=[x*y for x in a for y in b];return min(v),max(v)
def inverse(a):
    if a[0]<=0<=a[1]:raise ValueError('zero denominator')
    return 1/a[1],1/a[0]
def power(a,n):
    if n<0:return power(inverse(a),-n)
    out=interval(1)
    while n:
        if n&1:out=mul(out,a)
        a=mul(a,a);n//=2
    return out

def sqrt_endpoint(x):
    if x<0:raise ValueError('negative radicand')
    m=math.isqrt((x.numerator*SCALE*SCALE)//x.denominator)
    lo=F(m,SCALE)
    hi=lo if lo*lo==x else F(m+1,SCALE)
    assert lo*lo<=x<=hi*hi
    return lo,hi

def root(a):return sqrt_endpoint(a[0])[0],sqrt_endpoint(a[1])[1]

def enclose(e):
    if e.is_Rational:return interval(F(int(e.p),int(e.q)))
    if e.is_Add:
        out=interval(0)
        for x in e.args:out=add(out,enclose(x))
        return out
    if e.is_Mul:
        out=interval(1)
        for x in e.args:out=mul(out,enclose(x))
        return out
    if e.is_Pow:
        a,n=e.args
        if n.is_Integer:return power(enclose(a),int(n))
        if n.is_Rational and n.q==2:return power(root(enclose(a)),int(n.p))
    raise ValueError('unsupported exact expression: '+str(e))

def area(a,b,c):return S.sqrt(2*(a*a*b*b+b*b*c*c+c*c*a*a)-a**4-b**4-c**4)/4

def circle(a,b,r):return a*b*(a*S.sqrt(1-b*b/(4*r*r))+b*S.sqrt(1-a*a/(4*r*r)))/(4*r)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,default=ROOT/'verification/exact-identity-checks.json');a=ap.parse_args()
    k=(1+S.sqrt(5))/4;s=S.sqrt(10-2*S.sqrt(5))/4;ak=3*s*k*(1+k)/2
    x,t=S.symbols('x t',real=True);checks=[]
    def zero(name,e):
        value=S.simplify(S.expand(e));ok=value==0
        checks.append(dict(id=name,kind='EXACT_SYMBOLIC',passed=ok,residual=str(value)))
        if not ok:raise AssertionError(name+': '+str(value))
    def positive(name,e):
        lo,hi=enclose(e);ok=lo>0
        checks.append(dict(id=name,kind='EXACT_RATIONAL_ENCLOSURE',passed=ok,
          lower=str(lo),upper=str(hi),display=str(S.N(e,24))))
        if not ok:raise AssertionError(name+' not separated from zero by rational enclosure')
    zero('kappa_identity',4*k*k-2*k-1);zero('unit_circle',k*k+s*s-1)
    zero('density',5*k*s/(2*ak)-(5-S.sqrt(5))/3)
    u=S.Matrix([1+k,t]);v=S.Matrix([-2*s*t,6*k*s])
    zero('Gamma_diagonal',S.det(S.Matrix.hstack(u,v))/2-(2*ak+s*t*t))
    bb=S.Matrix([(6*k-1)/4-s*t,3*k*s+k*t]);dd=S.Matrix([(6*k-1)/4+s*t,-3*k*s+k*t])
    zero('Gamma_first_triangle',S.det(S.Matrix.hstack(u,bb))/2-(ak+t/4+s*t*t/2))
    zero('Gamma_second_triangle',-S.det(S.Matrix.hstack(u,dd))/2-(ak-t/4+s*t*t/2))
    p=s*x*x+(k-1)*x+s*(4*k+1)
    side2=[4*k*k+x*x,4*k*k+x*x/(4*k*k),(1+k)**2+(s-x)**2]
    H=2*sum(side2[i]*side2[j]for i,j in [(0,1),(1,2),(2,0)])-sum(z*z for z in side2)
    zero('Gamma_Heron_factor',H-4*p*p)
    zero('Gamma_root_discriminant',S.discriminant(p,x)+(13+15*S.sqrt(5))/8)
    zero('Gamma_raw_centered',(p+p.subs(x,2*s-x))/2-(2*ak+s*(x-s)**2))
    zero('Gamma_second_derivative',S.diff(2*ak+s*t*t,t,2)-2*s)
    A,B,T=S.symbols('A B T',positive=True)
    zero('trapezoid_area_second_derivative',S.diff((B+T)*S.sqrt(A*A-T*T),T,2)+(B*A*A+3*A*A*T-2*T**3)/(A*A-T*T)**S.Rational(3,2))
    zero('trapezoid_radius_derivative',S.diff(A*A*(A*A+B*B+2*B*T)/(4*(A*A-T*T)),T)-A*A*(B+T)*(A*A+B*T)/(2*(A*A-T*T)**2))
    refs=json.loads((ROOT/'tests/reference/paper_bounds.json').read_text())
    subs={S.Symbol('k'):k,S.Symbol('s'):s,S.Symbol('aK'):ak,S.Symbol('amin'):S.Rational(1237,1000),S.Symbol('epsN'):ak-S.Rational(1237,1000),S.Symbol('epsM'):S.Rational(1,125)}
    for r in refs:
        e=parse_mathematica(r['expression'])
        e=e.replace(lambda z:z.is_Function and str(z.func)=='triangleArea',lambda z:area(*z.args))
        e=e.replace(lambda z:z.is_Function and str(z.func)=='circleArea',lambda z:circle(*z.args))
        e=e.subs(subs)
        positive('paper_bound_'+r['id'],e)
    lo=k*S.sqrt(8);hi=4*k*S.sqrt(1-k*k/4);target=2*ak+4*(ak-S.Rational(1237,1000))
    grid=[lo+(hi-lo)*i/4 for i in range(5)]
    positive('case4_hi_below_3',3-hi)
    positive('case4_circular_derivative_lower',-2*k/(2*S.sqrt(7))+2*lo*S.sqrt(1-(2*k)**2/16))
    for i in range(4):positive('case4_uniform_cell_'+str(i+1),area(2*k,2*k,grid[i+1])+circle(2*k,grid[i],S.Integer(2))-target)
    a.output.parent.mkdir(parents=True,exist_ok=True)
    report=dict(scope='Independent selected symbolic identities and exact rational interval signs; not an OCaml/Wolfram run',sympy=S.__version__,sqrt_rounding_bits=BITS,checks=checks,total=len(checks),all_passed=all(q['passed']for q in checks))
    a.output.write_text(json.dumps(report,indent=2)+'\n');print('Exact symbolic/rational checks:',len(checks),'PASS. Report:',a.output)
if __name__=='__main__':main()
