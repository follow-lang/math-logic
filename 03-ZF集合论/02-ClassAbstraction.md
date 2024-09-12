
# Class Abstraction

```follow
term class cab(set s0, prop p0) { { s0 | p0 } }
```

```follow
axiom cab.def.1(set s0, set s1, prop p1) {
  |- iff(in(c(s0), cab(s1, p1)), subs(p1, s1, s0))
}
```

```follow
thm cab.def.1.ext(set s0, set s1, prop p1) {
  |- iff(subs(p1, s1, s0), in(c(s0), cab(s1, p1)))
  |- imp(in(c(s0), cab(s1, p1)), subs(p1, s1, s0))
  |- imp(subs(p1, s1, s0), in(c(s0), cab(s1, p1)))
} = {
  iff.comi(subs(p1,s1,s0), in(c(s0),cab(s1,p1)))
  iff.lefti(in(c(s0),cab(s1,p1)), subs(p1,s1,s0))
  iff.righti(subs(p1,s1,s0), in(c(s0),cab(s1,p1)))
  cab.def.1(s0, s1, p1)
}
```

## 性质

```follow
thm cab.id(prop p0, set s0) {
  |- iff(in(c(s0), cab(s0, p0)), p0)
  |- iff(p0, in(c(s0), cab(s0, p0)))
  |- imp(in(c(s0), cab(s0, p0)), p0)
  |- imp(p0, in(c(s0), cab(s0, p0)))
} = {
  iff.comi(p0, in(c(s0),cab(s0,p0)))
  iff.lefti(in(c(s0),cab(s0,p0)), p0)
  iff.righti(p0, in(c(s0),cab(s0,p0)))
  iff.syl(in(c(s0),cab(s0,p0)), p0, subs(p0,s0,s0))
  cab.def.1(s0, s0, p0)
  subs.id(p0, s0)
}
```

```follow
thm cab.a5.1(prop p0, set s0, set s1) {
  |- imp(in(c(s1), cab(s0, p0)), forall(s0, in(c(s1), cab(s0, p0))))
  diff (s0, s1)
} = {
  a5.rw(s0, in(c(s1),cab(s0,p0)), subs(p0,s0,s1))
  cab.def.1(s1, s0, p0)
  subs.a5(p0, s0, s1)
}
```

```follow
thm cab.nf.1(prop p0, set s0, set s1) {
  |- nf(s0, in(c(s1),cab(s0,p0)))
  diff (s0, s1)
} = {
  nf.introigen.2(s0, in(c(s1),cab(s0,p0)))
  cab.a5.1(p0, s0, s1)
}
```

```follow
thm cab.a5.2(prop p0, set s0, set s1, set s2) {
  |- imp(in(c(s1),cab(s0,p0)), forall(s2,in(c(s1),cab(s0,p0))))
  -| imp(p0, forall(s2, p0))
  diff (s1, s2)
} = {
  a5.rw(s2, in(c(s1),cab(s0,p0)), subs(p0,s0,s1))
  cab.def.1(s1, s0, p0)
  subs.forallsubs(p0, s0, s1, s2)
}
```

```follow
thm cab.nf.2(prop p0, set s0, set s1, set s2) {
  |- nf(s2, in(c(s1), cab(s0, p0)))
  -| nf(s2, p0)
  diff (s2, s1)
} = {
  nf.introigen.2(s2, in(c(s1),cab(s0,p0)))
  cab.a5.2(p0, s0, s1, s2)
  nf.a5(p0, s2)
}
```

# 定义Class之间的等价 

```follow
axiom eq.def(class c0, class c1, set s0) {
  |- iff(eq(c0,c1), forall(s0,iff(in(c(s0),c0), in(c(s0),c1))))
  diff (s0, c0) (s0, c1)
} 
```

```follow
thm eq.def.ext(class c0, class c1, set s0) {
  |- iff(forall(s0,iff(in(c(s0),c0), in(c(s0),c1))), eq(c0,c1))
  |- imp(eq(c0,c1), forall(s0,iff(in(c(s0),c0), in(c(s0),c1))))
  |- imp(forall(s0,iff(in(c(s0),c0), in(c(s0),c1))), eq(c0,c1))
  diff (s0, c0) (s0, c1)
} = {
  iff.comi(forall(s0,iff(in(c(s0),c0),in(c(s0),c1))), eq(c0,c1))
  iff.lefti(eq(c0,c1), forall(s0,iff(in(c(s0),c0),in(c(s0),c1))))
  iff.righti(forall(s0,iff(in(c(s0),c0),in(c(s0),c1))), eq(c0,c1))
  eq.def(c0, c1, s0)
}
```

```follow
thm eq.defigen(class c0, class c1, set s0) {
  |- eq(c0,c1)
  -| iff(in(c(s0),c0), in(c(s0),c1))
  diff (s0, c0) (s0, c1)
} = {
  mp(eq(c0,c1), forall(s0,iff(in(c(s0),c0),in(c(s0),c1))))
  eq.def.ext(c0, c1, s0)
  gen.forall(s0, iff(in(c(s0),c0),in(c(s0),c1)))
}
```

```follow
thm eq.defigend(class c0, class c1, set s0, prop p0) {
  |- imp(p0, eq(c0,c1))
  -| imp(p0, iff(in(c(s0),c0), in(c(s0),c1)))
  diff (s0, c0) (s0, c1) (s0, p0)
} = {
  syl(p0, eq(c0,c1), forall(s0,iff(in(c(s0),c0),in(c(s0),c1))))
  eq.def.ext(c0, c1, s0)
  gend(s0, iff(in(c(s0),c0),in(c(s0),c1)), p0)
}
```

```follow
thm eq.defgen(class c0, class c1, set s0) {
  |- imp(eq(c0,c1), iff(in(c(s0),c0), in(c(s0),c1)))
  diff (s0, c0) (s0, c1)
} = {
  syl(eq(c0,c1), iff(in(c(s0),c0),in(c(s0),c1)), forall(s0,iff(in(c(s0),c0),in(c(s0),c1))))
  eq.def.ext(c0, c1, s0)
  special.2(iff(in(c(s0),c0),in(c(s0),c1)), s0)
}
```

```follow
thm eq.id.class(class c0) {
  |- eq(c0, c0)
} = {
  eq.defigen(c0, c0, hs0)
  iff.id(in(c(hs0),c0))
}
```

```follow
thm eq.idd.class(class c0, prop p0) {
  |- imp(p0, eq(c0, c0))
} = {
  a1i(p0, eq(c0,c0))
  eq.id.class(c0)
}
```

```follow
thm eq.com.class(class c0, class c1) {
  |- imp(eq(c0, c1), eq(c1, c0))
} = {
  eq.defigend(c1, c0, hs0, eq(c0,c1))
  iff.comid(eq(c0,c1), in(c(hs0),c1), in(c(hs0),c0))
  eq.defgen(c0, c1, hs0)
}
```

```follow
thm eq.comi.class(class c0, class c1) {
  |- eq(c0, c1)
  -| eq(c1, c0)
} = {
  mp(eq(c0,c1), eq(c1,c0))
  eq.com.class(c1, c0)
}
```

```follow
thm eq.comid.class(class c0, class c1, prop p0) {
  |- imp(p0, eq(c0, c1))
  -| imp(p0, eq(c1, c0))
} = {
  syl(p0, eq(c0,c1), eq(c1,c0))
  eq.com.class(c1, c0)
}
```

```follow
thm eq.com.class.iff(class c0, class c1) {
  |- iff(eq(c0, c1), eq(c1, c0))
} = {
  iff.introii.1(eq(c0,c1), eq(c1,c0))
  eq.com.class(c0, c1)
  eq.com.class(c1, c0)
}
```

```follow
thm eq.trans.class.iff.1(class c0, class c1, class c2) {
  |- imp(eq(c0, c1), iff(eq(c0, c2), eq(c1, c2)))
} = {
  iff.rw23(eq(c0,c1), eq(c0,c2), eq(c1,c2), forall(hs0,iff(in(c(hs0),c0),in(c(hs0),c2))), forall(hs0,iff(in(c(hs0),c1),in(c(hs0),c2))))
  eq.def(c0, c2, hs0)
  eq.def(c1, c2, hs0)
  a4id.aaa.iff(hs0, iff(in(c(hs0),c0),in(c(hs0),c2)), iff(in(c(hs0),c1),in(c(hs0),c2)), eq(c0,c1))
  a4igen.diff.aaa.2(hs0, iff(iff(in(c(hs0),c0),in(c(hs0),c2)),iff(in(c(hs0),c1),in(c(hs0),c2))), eq(c0,c1))
  iff.transid.2(in(c(hs0),c1), in(c(hs0),c0), in(c(hs0),c2), eq(c0,c1))
  iff.comid(eq(c0,c1), in(c(hs0),c1), in(c(hs0),c0))
  eq.defgen(c0, c1, hs0)
}
```

```follow
thm eq.trans.class.iff.2(class c0, class c1, class c2) {
  |- imp(eq(c0, c1), iff(eq(c0, c2), eq(c2, c1)))
  |- imp(eq(c0, c1), iff(eq(c2, c0), eq(c1, c2)))
  |- imp(eq(c0, c1), iff(eq(c2, c0), eq(c2, c1)))
  |- imp(eq(c0, c1), iff(eq(c1, c2), eq(c0, c2)))
  |- imp(eq(c0, c1), iff(eq(c2, c1), eq(c0, c2)))
  |- imp(eq(c0, c1), iff(eq(c1, c2), eq(c2, c0)))
  |- imp(eq(c0, c1), iff(eq(c2, c1), eq(c2, c0)))
} = {
  iff.comid(eq(c0,c1), eq(c1,c2), eq(c0,c2))
  iff.comid(eq(c0,c1), eq(c2,c1), eq(c0,c2))
  iff.comid(eq(c0,c1), eq(c2,c0), eq(c2,c1))
  iff.comid(eq(c0,c1), eq(c1,c2), eq(c2,c0))
  iff.comid(eq(c0,c1), eq(c2,c1), eq(c2,c0))

  iff.rw3(eq(c0,c1), eq(c2,c0), eq(c2,c1), eq(c1,c2))
  eq.com.class.iff(c2, c1)
  iff.rw3(eq(c0,c1), eq(c0,c2), eq(c2,c1), eq(c1,c2))
  eq.com.class.iff(c2, c1)
  iff.rw2(eq(c0,c1), eq(c2,c0), eq(c1,c2), eq(c0,c2))
  eq.com.class.iff(c2, c0)

  eq.trans.class.iff.1(c0, c1, c2)
}
```

```follow
thm eq.trans.class(class c0, class c1, class c2) {
  |- imp(eq(c0, c1), imp(eq(c0, c2), eq(c1, c2)))
  |- imp(eq(c0, c1), imp(eq(c0, c2), eq(c2, c1)))
  |- imp(eq(c0, c1), imp(eq(c2, c0), eq(c1, c2)))
  |- imp(eq(c0, c1), imp(eq(c2, c0), eq(c2, c1)))
  |- imp(eq(c0, c1), imp(eq(c1, c2), eq(c0, c2)))
  |- imp(eq(c0, c1), imp(eq(c2, c1), eq(c0, c2)))
  |- imp(eq(c0, c1), imp(eq(c1, c2), eq(c2, c0)))
  |- imp(eq(c0, c1), imp(eq(c2, c1), eq(c2, c0)))
} = {
  iff.leftid(eq(c0,c1), eq(c0,c2), eq(c1,c2))
  iff.leftid(eq(c0,c1), eq(c0,c2), eq(c2,c1))
  iff.leftid(eq(c0,c1), eq(c2,c0), eq(c1,c2))
  iff.leftid(eq(c0,c1), eq(c2,c0), eq(c2,c1))
  iff.leftid(eq(c0,c1), eq(c1,c2), eq(c0,c2))
  iff.leftid(eq(c0,c1), eq(c2,c1), eq(c0,c2))
  iff.leftid(eq(c0,c1), eq(c1,c2), eq(c2,c0))
  iff.leftid(eq(c0,c1), eq(c2,c1), eq(c2,c0))
  eq.trans.class.iff.1(c0, c1, c2)
  eq.trans.class.iff.2(c0, c1, c2)
}
```

```follow
thm eq.trans.and.class(class c0, class c1, class c2) {
  |- imp(and(eq(c0, c1), eq(c0, c2)), eq(c1, c2))
  |- imp(and(eq(c0, c1), eq(c0, c2)), eq(c2, c1))
  |- imp(and(eq(c0, c1), eq(c2, c0)), eq(c1, c2))
  |- imp(and(eq(c0, c1), eq(c2, c0)), eq(c2, c1))
  |- imp(and(eq(c0, c1), eq(c1, c2)), eq(c0, c2))
  |- imp(and(eq(c0, c1), eq(c2, c1)), eq(c0, c2))
  |- imp(and(eq(c0, c1), eq(c1, c2)), eq(c2, c0))
  |- imp(and(eq(c0, c1), eq(c2, c1)), eq(c2, c0))
} = {
  and.joini(eq(c0,c1), eq(c0,c2), eq(c1,c2))
  and.joini(eq(c0,c1), eq(c0,c2), eq(c2,c1))
  and.joini(eq(c0,c1), eq(c2,c0), eq(c1,c2))
  and.joini(eq(c0,c1), eq(c2,c0), eq(c2,c1))
  and.joini(eq(c0,c1), eq(c1,c2), eq(c0,c2))
  and.joini(eq(c0,c1), eq(c2,c1), eq(c0,c2))
  and.joini(eq(c0,c1), eq(c1,c2), eq(c2,c0))
  and.joini(eq(c0,c1), eq(c2,c1), eq(c2,c0))
  eq.trans.class(c0, c1, c2)
}
```

```follow
thm eq.transi.class(class c0, class c1, class c2) {
  |- imp(eq(c0, c2), eq(c1, c2))
  |- imp(eq(c0, c2), eq(c2, c1))
  |- imp(eq(c2, c0), eq(c1, c2))
  |- imp(eq(c2, c0), eq(c2, c1))
  |- imp(eq(c1, c2), eq(c0, c2))
  |- imp(eq(c2, c1), eq(c0, c2))
  |- imp(eq(c1, c2), eq(c2, c0))
  |- imp(eq(c2, c1), eq(c2, c0))
  -| eq(c0, c1)
} = {
  mp(imp(eq(c0,c2),eq(c1,c2)), eq(c0,c1))
  mp(imp(eq(c0,c2),eq(c2,c1)), eq(c0,c1))
  mp(imp(eq(c2,c0),eq(c1,c2)), eq(c0,c1))
  mp(imp(eq(c2,c0),eq(c2,c1)), eq(c0,c1))
  mp(imp(eq(c1,c2),eq(c0,c2)), eq(c0,c1))
  mp(imp(eq(c2,c1),eq(c0,c2)), eq(c0,c1))
  mp(imp(eq(c1,c2),eq(c2,c0)), eq(c0,c1))
  mp(imp(eq(c2,c1),eq(c2,c0)), eq(c0,c1))
  eq.trans.class(c0, c1, c2)
}
```

```follow
thm eq.transid.class(class c0, class c1, class c2, prop p0) {
  |- imp(p0, imp(eq(c0, c2), eq(c1, c2)))
  |- imp(p0, imp(eq(c0, c2), eq(c2, c1)))
  |- imp(p0, imp(eq(c2, c0), eq(c1, c2)))
  |- imp(p0, imp(eq(c2, c0), eq(c2, c1)))
  |- imp(p0, imp(eq(c1, c2), eq(c0, c2)))
  |- imp(p0, imp(eq(c2, c1), eq(c0, c2)))
  |- imp(p0, imp(eq(c1, c2), eq(c2, c0)))
  |- imp(p0, imp(eq(c2, c1), eq(c2, c0)))
  -| imp(p0, eq(c0, c1))
} = {
  syl(p0, imp(eq(c0,c2),eq(c1,c2)), eq(c0,c1))
  syl(p0, imp(eq(c0,c2),eq(c2,c1)), eq(c0,c1))
  syl(p0, imp(eq(c2,c0),eq(c1,c2)), eq(c0,c1))
  syl(p0, imp(eq(c2,c0),eq(c2,c1)), eq(c0,c1))
  syl(p0, imp(eq(c1,c2),eq(c0,c2)), eq(c0,c1))
  syl(p0, imp(eq(c2,c1),eq(c0,c2)), eq(c0,c1))
  syl(p0, imp(eq(c1,c2),eq(c2,c0)), eq(c0,c1))
  syl(p0, imp(eq(c2,c1),eq(c2,c0)), eq(c0,c1))
  eq.trans.class(c0, c1, c2)
}
```

```follow
thm eq.transi.iff.class(class c0, class c1, class c2) {
  |- iff(eq(c0, c2), eq(c1, c2))
  |- iff(eq(c0, c2), eq(c2, c1))
  |- iff(eq(c2, c0), eq(c1, c2))
  |- iff(eq(c2, c0), eq(c2, c1))
  |- iff(eq(c1, c2), eq(c0, c2))
  |- iff(eq(c2, c1), eq(c0, c2))
  |- iff(eq(c1, c2), eq(c2, c0))
  |- iff(eq(c2, c1), eq(c2, c0))
  -| eq(c0, c1)
} = {
  mp(iff(eq(c0,c2),eq(c1,c2)), eq(c0,c1))
  mp(iff(eq(c0,c2),eq(c2,c1)), eq(c0,c1))
  mp(iff(eq(c2,c0),eq(c1,c2)), eq(c0,c1))
  mp(iff(eq(c2,c0),eq(c2,c1)), eq(c0,c1))
  mp(iff(eq(c1,c2),eq(c0,c2)), eq(c0,c1))
  mp(iff(eq(c2,c1),eq(c0,c2)), eq(c0,c1))
  mp(iff(eq(c1,c2),eq(c2,c0)), eq(c0,c1))
  mp(iff(eq(c2,c1),eq(c2,c0)), eq(c0,c1))
  eq.trans.class.iff.1(c0, c1, c2)
  eq.trans.class.iff.2(c0, c1, c2)
}
```

```follow
thm eq.transid.iff.class(class c0, class c1, class c2, prop p0) {
  |- imp(p0, iff(eq(c0, c2), eq(c1, c2)))
  |- imp(p0, iff(eq(c0, c2), eq(c2, c1)))
  |- imp(p0, iff(eq(c2, c0), eq(c1, c2)))
  |- imp(p0, iff(eq(c2, c0), eq(c2, c1)))
  |- imp(p0, iff(eq(c1, c2), eq(c0, c2)))
  |- imp(p0, iff(eq(c2, c1), eq(c0, c2)))
  |- imp(p0, iff(eq(c1, c2), eq(c2, c0)))
  |- imp(p0, iff(eq(c2, c1), eq(c2, c0)))
  -| imp(p0, eq(c0, c1))
} = {
  syl(p0, iff(eq(c0,c2),eq(c1,c2)), eq(c0,c1))
  syl(p0, iff(eq(c0,c2),eq(c2,c1)), eq(c0,c1))
  syl(p0, iff(eq(c2,c0),eq(c1,c2)), eq(c0,c1))
  syl(p0, iff(eq(c2,c0),eq(c2,c1)), eq(c0,c1))
  syl(p0, iff(eq(c1,c2),eq(c0,c2)), eq(c0,c1))
  syl(p0, iff(eq(c2,c1),eq(c0,c2)), eq(c0,c1))
  syl(p0, iff(eq(c1,c2),eq(c2,c0)), eq(c0,c1))
  syl(p0, iff(eq(c2,c1),eq(c2,c0)), eq(c0,c1))
  eq.trans.class.iff.1(c0, c1, c2)
  eq.trans.class.iff.2(c0, c1, c2)
}
```

```follow
thm eq.transii.class(class c0, class c1, class c2) {
  |- eq(c0, c1)
  -| eq(c0, c2)
  -| eq(c2, c1)
} = {
  mp(eq(c0,c1), eq(c0,c2))
  eq.transi.class(c2, c1, c0)
}
```

```follow
thm eq.transiid.class(class c0, class c1, class c2, prop p0) {
  |- imp(p0, eq(c0, c1))
  -| imp(p0, eq(c0, c2))
  -| imp(p0, eq(c2, c1))
} = {
  mpd(p0, eq(c0,c1), eq(c0,c2))
  eq.transid.class(c2, c1, c0, p0)
}
```

```follow
thm eq.2eq.class.1(class c0, class c1, class c2, class c3) {
  |- imp(eq(c0,c2), imp(eq(c1,c3),imp(eq(c0,c1), eq(c2,c3))))
  |- imp(eq(c2,c0), imp(eq(c1,c3),imp(eq(c0,c1), eq(c2,c3))))
  |- imp(eq(c0,c2), imp(eq(c3,c1),imp(eq(c0,c1), eq(c2,c3))))
  |- imp(eq(c2,c0), imp(eq(c3,c1),imp(eq(c0,c1), eq(c2,c3))))

  |- imp(eq(c1,c3), imp(eq(c0,c2), imp(eq(c0,c1), eq(c2,c3))))
  |- imp(eq(c1,c3), imp(eq(c2,c0), imp(eq(c0,c1), eq(c2,c3))))
  |- imp(eq(c3,c1), imp(eq(c0,c2), imp(eq(c0,c1), eq(c2,c3))))
  |- imp(eq(c3,c1), imp(eq(c2,c0), imp(eq(c0,c1), eq(c2,c3))))
} = {
  com12i(eq(c1,c3), eq(c0,c2), imp(eq(c0,c1),eq(c2,c3)))
  com12i(eq(c1,c3), eq(c2,c0), imp(eq(c0,c1),eq(c2,c3)))
  com12i(eq(c3,c1), eq(c0,c2), imp(eq(c0,c1),eq(c2,c3)))
  com12i(eq(c3,c1), eq(c2,c0), imp(eq(c0,c1),eq(c2,c3)))
  
  syl(eq(c2,c0), imp(eq(c3,c1),imp(eq(c0,c1),eq(c2,c3))), eq(c0,c2))
  eq.com.class(c2, c0)
  rw2(eq(c0,c2), eq(c3,c1), imp(eq(c0,c1),eq(c2,c3)), eq(c1,c3))
  eq.com.class(c3, c1)
  syl(eq(c2,c0), imp(eq(c1,c3),imp(eq(c0,c1),eq(c2,c3))), eq(c0,c2))
  eq.com.class(c2, c0)
  com12id(eq(c0,c2), eq(c1,c3), eq(c0,c1), eq(c2,c3))
  rw3(eq(c0,c2), eq(c0,c1), imp(eq(c1,c3),eq(c2,c3)), eq(c2,c1))
  eq.trans.class(c0, c2, c1)
  eq.trans.class(c2, c1, c3)
}
```

```follow
thm eq.2eq.class.2(class c0, class c1, class c2, class c3) {
  |- imp(eq(c0,c3), imp(eq(c1,c2),imp(eq(c0,c1), eq(c2,c3))))
  |- imp(eq(c3,c0), imp(eq(c1,c2),imp(eq(c0,c1), eq(c2,c3))))
  |- imp(eq(c0,c3), imp(eq(c2,c1),imp(eq(c0,c1), eq(c2,c3))))
  |- imp(eq(c3,c0), imp(eq(c2,c1),imp(eq(c0,c1), eq(c2,c3))))

  |- imp(eq(c1,c2), imp(eq(c0,c3), imp(eq(c0,c1), eq(c2,c3))))
  |- imp(eq(c1,c2), imp(eq(c3,c0), imp(eq(c0,c1), eq(c2,c3))))
  |- imp(eq(c2,c1), imp(eq(c0,c3), imp(eq(c0,c1), eq(c2,c3))))
  |- imp(eq(c2,c1), imp(eq(c3,c0), imp(eq(c0,c1), eq(c2,c3))))
} = {
  com12i(eq(c1,c2), eq(c0,c3), imp(eq(c0,c1),eq(c2,c3)))
  com12i(eq(c1,c2), eq(c3,c0), imp(eq(c0,c1),eq(c2,c3)))
  com12i(eq(c2,c1), eq(c0,c3), imp(eq(c0,c1),eq(c2,c3)))
  com12i(eq(c2,c1), eq(c3,c0), imp(eq(c0,c1),eq(c2,c3)))
  syl(eq(c3,c0), imp(eq(c2,c1),imp(eq(c0,c1),eq(c2,c3))), eq(c0,c3))
  eq.com.class(c3, c0)
  rw2(eq(c0,c3), eq(c2,c1), imp(eq(c0,c1),eq(c2,c3)), eq(c1,c2))
  eq.com.class(c2, c1)
  syl(eq(c3,c0), imp(eq(c1,c2),imp(eq(c0,c1),eq(c2,c3))), eq(c0,c3))
  eq.com.class(c3, c0)
  com12id(eq(c0,c3), eq(c1,c2), eq(c0,c1), eq(c2,c3))
  rw3(eq(c0,c3), eq(c0,c1), imp(eq(c1,c2),eq(c2,c3)), eq(c3,c1))
  eq.trans.class(c0, c3, c1)
  eq.trans.class(c3, c1, c2)
}
```

```follow
thm eq.2eq.class.and.1(class c0, class c1, class c2, class c3) {
  |- imp(and(eq(c0,c2), eq(c1,c3)),imp(eq(c0,c1), eq(c2,c3)))
  |- imp(and(eq(c2,c0), eq(c1,c3)),imp(eq(c0,c1), eq(c2,c3)))
  |- imp(and(eq(c0,c2), eq(c3,c1)),imp(eq(c0,c1), eq(c2,c3)))
  |- imp(and(eq(c2,c0), eq(c3,c1)),imp(eq(c0,c1), eq(c2,c3)))

  |- imp(and(eq(c1,c3), eq(c0,c2)), imp(eq(c0,c1), eq(c2,c3)))
  |- imp(and(eq(c1,c3), eq(c2,c0)), imp(eq(c0,c1), eq(c2,c3)))
  |- imp(and(eq(c3,c1), eq(c0,c2)), imp(eq(c0,c1), eq(c2,c3)))
  |- imp(and(eq(c3,c1), eq(c2,c0)), imp(eq(c0,c1), eq(c2,c3)))
} = {
  and.joini(eq(c0,c2), eq(c1,c3), imp(eq(c0,c1),eq(c2,c3)))
  and.joini(eq(c2,c0), eq(c1,c3), imp(eq(c0,c1),eq(c2,c3)))
  and.joini(eq(c0,c2), eq(c3,c1), imp(eq(c0,c1),eq(c2,c3)))
  and.joini(eq(c2,c0), eq(c3,c1), imp(eq(c0,c1),eq(c2,c3)))
  and.joini(eq(c1,c3), eq(c0,c2), imp(eq(c0,c1),eq(c2,c3)))
  and.joini(eq(c1,c3), eq(c2,c0), imp(eq(c0,c1),eq(c2,c3)))
  and.joini(eq(c3,c1), eq(c0,c2), imp(eq(c0,c1),eq(c2,c3)))
  and.joini(eq(c3,c1), eq(c2,c0), imp(eq(c0,c1),eq(c2,c3)))
  eq.2eq.class.1(c0, c1, c2, c3)
}
```

```follow
thm eq.2eq.class.and.2(class c0, class c1, class c2, class c3) {
  |- imp(and(eq(c0,c3), eq(c1,c2)),imp(eq(c0,c1), eq(c2,c3)))
  |- imp(and(eq(c3,c0), eq(c1,c2)),imp(eq(c0,c1), eq(c2,c3)))
  |- imp(and(eq(c0,c3), eq(c2,c1)),imp(eq(c0,c1), eq(c2,c3)))
  |- imp(and(eq(c3,c0), eq(c2,c1)),imp(eq(c0,c1), eq(c2,c3)))

  |- imp(and(eq(c1,c2), eq(c0,c3)), imp(eq(c0,c1), eq(c2,c3)))
  |- imp(and(eq(c1,c2), eq(c3,c0)), imp(eq(c0,c1), eq(c2,c3)))
  |- imp(and(eq(c2,c1), eq(c0,c3)), imp(eq(c0,c1), eq(c2,c3)))
  |- imp(and(eq(c2,c1), eq(c3,c0)), imp(eq(c0,c1), eq(c2,c3)))
} = {
  and.joini(eq(c0,c3), eq(c1,c2), imp(eq(c0,c1),eq(c2,c3)))
  and.joini(eq(c3,c0), eq(c1,c2), imp(eq(c0,c1),eq(c2,c3)))
  and.joini(eq(c0,c3), eq(c2,c1), imp(eq(c0,c1),eq(c2,c3)))
  and.joini(eq(c3,c0), eq(c2,c1), imp(eq(c0,c1),eq(c2,c3)))
  and.joini(eq(c1,c2), eq(c0,c3), imp(eq(c0,c1),eq(c2,c3)))
  and.joini(eq(c1,c2), eq(c3,c0), imp(eq(c0,c1),eq(c2,c3)))
  and.joini(eq(c2,c1), eq(c0,c3), imp(eq(c0,c1),eq(c2,c3)))
  and.joini(eq(c2,c1), eq(c3,c0), imp(eq(c0,c1),eq(c2,c3)))
  eq.2eq.class.2(c0, c1, c2, c3)
}
```

```follow
thm eq.2eqii.class.1(class c0, class c1, class c2, class c3) {
  |- imp(eq(c0,c1), eq(c2,c3))
  -| eq(c0,c2)
  -| eq(c1,c3)
} = {
  mp(imp(eq(c0,c1),eq(c2,c3)), eq(c1,c3))
  mp(imp(eq(c1,c3),imp(eq(c0,c1),eq(c2,c3))), eq(c0,c2))
  eq.2eq.class.1(c0, c1, c2, c3)
}
```

```follow
thm eq.2eqiid.class.1(class c0, class c1, class c2, class c3, prop p0) {
  |- imp(p0, imp(eq(c0,c1), eq(c2,c3)))
  -| imp(p0, eq(c0,c2))
  -| imp(p0, eq(c1,c3))
} = {
  mpd(p0, imp(eq(c0,c1),eq(c2,c3)), eq(c1,c3))
  syl(p0, imp(eq(c1,c3),imp(eq(c0,c1),eq(c2,c3))), eq(c0,c2))
  eq.2eq.class.1(c0, c1, c2, c3)
}
```

```follow
thm eq.2eqii.class.2(class c0, class c1, class c2, class c3) {
  |- imp(eq(c0,c1), eq(c2,c3))
  -| eq(c0,c3)
  -| eq(c1,c2)
} = {
  mp(imp(eq(c0,c1),eq(c2,c3)), eq(c0,c3))
  mp(imp(eq(c0,c3),imp(eq(c0,c1),eq(c2,c3))), eq(c1,c2))
  eq.2eq.class.2(c0, c1, c2, c3)
}
```

```follow
thm eq.2eqiid.class.2(class c0, class c1, class c2, class c3, prop p0) {
  |- imp(p0, imp(eq(c0,c1), eq(c2,c3)))
  -| imp(p0, eq(c0,c3))
  -| imp(p0, eq(c1,c2))
} = {
  mpd(p0, imp(eq(c0,c1),eq(c2,c3)), eq(c0,c3))
  syl(p0, imp(eq(c0,c3),imp(eq(c0,c1),eq(c2,c3))), eq(c1,c2))
  eq.2eq.class.2(c0, c1, c2, c3)
}
```

```follow
thm eq.iffeq.and.class(class c0, class c1, class c2, class c3) {
  |- imp(and(eq(c0,c2), eq(c1,c3)), iff(eq(c0,c1), eq(c2,c3)))
  |- imp(and(eq(c2,c0), eq(c1,c3)), iff(eq(c0,c1), eq(c2,c3)))
  |- imp(and(eq(c0,c2), eq(c3,c1)), iff(eq(c0,c1), eq(c2,c3)))
  |- imp(and(eq(c2,c0), eq(c3,c1)), iff(eq(c0,c1), eq(c2,c3)))
  |- imp(and(eq(c1,c3), eq(c0,c2)), iff(eq(c0,c1), eq(c2,c3)))
  |- imp(and(eq(c1,c3), eq(c2,c0)), iff(eq(c0,c1), eq(c2,c3)))
  |- imp(and(eq(c3,c1), eq(c0,c2)), iff(eq(c0,c1), eq(c2,c3)))
  |- imp(and(eq(c3,c1), eq(c2,c0)), iff(eq(c0,c1), eq(c2,c3)))
  |- imp(and(eq(c0,c3), eq(c1,c2)), iff(eq(c0,c1), eq(c2,c3)))
  |- imp(and(eq(c3,c0), eq(c1,c2)), iff(eq(c0,c1), eq(c2,c3)))
  |- imp(and(eq(c0,c3), eq(c2,c1)), iff(eq(c0,c1), eq(c2,c3)))
  |- imp(and(eq(c3,c0), eq(c2,c1)), iff(eq(c0,c1), eq(c2,c3)))
  |- imp(and(eq(c1,c2), eq(c0,c3)), iff(eq(c0,c1), eq(c2,c3)))
  |- imp(and(eq(c1,c2), eq(c3,c0)), iff(eq(c0,c1), eq(c2,c3)))
  |- imp(and(eq(c2,c1), eq(c0,c3)), iff(eq(c0,c1), eq(c2,c3)))
  |- imp(and(eq(c2,c1), eq(c3,c0)), iff(eq(c0,c1), eq(c2,c3)))
} = {
  iff.introiid.1(and(eq(c0,c2),eq(c1,c3)), eq(c0,c1), eq(c2,c3))
  iff.introiid.1(and(eq(c2,c0),eq(c1,c3)), eq(c0,c1), eq(c2,c3))
  iff.introiid.1(and(eq(c0,c2),eq(c3,c1)), eq(c0,c1), eq(c2,c3))
  iff.introiid.1(and(eq(c2,c0),eq(c3,c1)), eq(c0,c1), eq(c2,c3))
  iff.introiid.1(and(eq(c1,c3),eq(c0,c2)), eq(c0,c1), eq(c2,c3))
  iff.introiid.1(and(eq(c1,c3),eq(c2,c0)), eq(c0,c1), eq(c2,c3))
  iff.introiid.1(and(eq(c3,c1),eq(c0,c2)), eq(c0,c1), eq(c2,c3))
  iff.introiid.1(and(eq(c3,c1),eq(c2,c0)), eq(c0,c1), eq(c2,c3))
  iff.introiid.1(and(eq(c0,c3),eq(c1,c2)), eq(c0,c1), eq(c2,c3))
  iff.introiid.1(and(eq(c3,c0),eq(c1,c2)), eq(c0,c1), eq(c2,c3))
  iff.introiid.1(and(eq(c0,c3),eq(c2,c1)), eq(c0,c1), eq(c2,c3))
  iff.introiid.1(and(eq(c3,c0),eq(c2,c1)), eq(c0,c1), eq(c2,c3))
  iff.introiid.1(and(eq(c1,c2),eq(c0,c3)), eq(c0,c1), eq(c2,c3))
  iff.introiid.1(and(eq(c1,c2),eq(c3,c0)), eq(c0,c1), eq(c2,c3))
  iff.introiid.1(and(eq(c2,c1),eq(c0,c3)), eq(c0,c1), eq(c2,c3))
  iff.introiid.1(and(eq(c2,c1),eq(c3,c0)), eq(c0,c1), eq(c2,c3))
  eq.2eq.class.and.1(c0, c1, c2, c3)
  eq.2eq.class.and.1(c2, c3, c0, c1)
  eq.2eq.class.and.2(c0, c1, c2, c3)
  eq.2eq.class.and.2(c2, c3, c0, c1)
}
```

```follow
thm eq.iffeq.class(class c0, class c1, class c2, class c3) {
  |- imp(eq(c0,c2), imp(eq(c1,c3), iff(eq(c0,c1), eq(c2,c3))))
  |- imp(eq(c2,c0), imp(eq(c1,c3), iff(eq(c0,c1), eq(c2,c3))))
  |- imp(eq(c0,c2), imp(eq(c3,c1), iff(eq(c0,c1), eq(c2,c3))))
  |- imp(eq(c2,c0), imp(eq(c3,c1), iff(eq(c0,c1), eq(c2,c3))))
  |- imp(eq(c1,c3), imp(eq(c0,c2), iff(eq(c0,c1), eq(c2,c3))))
  |- imp(eq(c1,c3), imp(eq(c2,c0), iff(eq(c0,c1), eq(c2,c3))))
  |- imp(eq(c3,c1), imp(eq(c0,c2), iff(eq(c0,c1), eq(c2,c3))))
  |- imp(eq(c3,c1), imp(eq(c2,c0), iff(eq(c0,c1), eq(c2,c3))))
  |- imp(eq(c0,c3), imp(eq(c1,c2), iff(eq(c0,c1), eq(c2,c3))))
  |- imp(eq(c3,c0), imp(eq(c1,c2), iff(eq(c0,c1), eq(c2,c3))))
  |- imp(eq(c0,c3), imp(eq(c2,c1), iff(eq(c0,c1), eq(c2,c3))))
  |- imp(eq(c3,c0), imp(eq(c2,c1), iff(eq(c0,c1), eq(c2,c3))))
  |- imp(eq(c1,c2), imp(eq(c0,c3), iff(eq(c0,c1), eq(c2,c3))))
  |- imp(eq(c1,c2), imp(eq(c3,c0), iff(eq(c0,c1), eq(c2,c3))))
  |- imp(eq(c2,c1), imp(eq(c0,c3), iff(eq(c0,c1), eq(c2,c3))))
  |- imp(eq(c2,c1), imp(eq(c3,c0), iff(eq(c0,c1), eq(c2,c3))))
} = {
  and.spliti(eq(c0,c2), eq(c1,c3), iff(eq(c0,c1),eq(c2,c3)))
  and.spliti(eq(c2,c0), eq(c1,c3), iff(eq(c0,c1),eq(c2,c3)))
  and.spliti(eq(c0,c2), eq(c3,c1), iff(eq(c0,c1),eq(c2,c3)))
  and.spliti(eq(c2,c0), eq(c3,c1), iff(eq(c0,c1),eq(c2,c3)))
  and.spliti(eq(c1,c3), eq(c0,c2), iff(eq(c0,c1),eq(c2,c3)))
  and.spliti(eq(c1,c3), eq(c2,c0), iff(eq(c0,c1),eq(c2,c3)))
  and.spliti(eq(c3,c1), eq(c0,c2), iff(eq(c0,c1),eq(c2,c3)))
  and.spliti(eq(c3,c1), eq(c2,c0), iff(eq(c0,c1),eq(c2,c3)))
  and.spliti(eq(c0,c3), eq(c1,c2), iff(eq(c0,c1),eq(c2,c3)))
  and.spliti(eq(c3,c0), eq(c1,c2), iff(eq(c0,c1),eq(c2,c3)))
  and.spliti(eq(c0,c3), eq(c2,c1), iff(eq(c0,c1),eq(c2,c3)))
  and.spliti(eq(c3,c0), eq(c2,c1), iff(eq(c0,c1),eq(c2,c3)))
  and.spliti(eq(c1,c2), eq(c0,c3), iff(eq(c0,c1),eq(c2,c3)))
  and.spliti(eq(c1,c2), eq(c3,c0), iff(eq(c0,c1),eq(c2,c3)))
  and.spliti(eq(c2,c1), eq(c0,c3), iff(eq(c0,c1),eq(c2,c3)))
  and.spliti(eq(c2,c1), eq(c3,c0), iff(eq(c0,c1),eq(c2,c3)))
  eq.iffeq.and.class(c0, c1, c2, c3)
}
```

```follow
thm eq.iffeqii.class.1(class c0, class c1, class c2, class c3) {
  |- iff(eq(c0,c1), eq(c2,c3))
  -| eq(c0,c2)
  -| eq(c1,c3)
} = {
  mp(iff(eq(c0,c1),eq(c2,c3)), eq(c0,c2))
  mp(imp(eq(c0,c2),iff(eq(c0,c1),eq(c2,c3))), eq(c1,c3))
  eq.iffeq.class(c0, c1, c2, c3)
}
```

```follow
thm eq.iffeqiid.class.1(class c0, class c1, class c2, class c3, prop p0) {
  |- imp(p0, iff(eq(c0,c1), eq(c2,c3)))
  -| imp(p0, eq(c0,c2))
  -| imp(p0, eq(c1,c3))
} = {
  mpd(p0, iff(eq(c0,c1),eq(c2,c3)), eq(c0,c2))
  syl(p0, imp(eq(c0,c2),iff(eq(c0,c1),eq(c2,c3))), eq(c1,c3))
  eq.iffeq.class(c0, c1, c2, c3)
}
```

```follow
thm eq.iffeqii.class.2(class c0, class c1, class c2, class c3) {
  |- iff(eq(c0,c1), eq(c2,c3))
  -| eq(c0,c3)
  -| eq(c1,c2)
} = {
  mp(iff(eq(c0,c1),eq(c2,c3)), eq(c0,c3))
  mp(imp(eq(c0,c3),iff(eq(c0,c1),eq(c2,c3))), eq(c1,c2))
  eq.iffeq.class(c0, c1, c2, c3)
}
```

```follow
thm eq.iffeqiid.class.2(class c0, class c1, class c2, class c3, prop p0) {
  |- imp(p0, iff(eq(c0,c1), eq(c2,c3)))
  -| imp(p0, eq(c0,c3))
  -| imp(p0, eq(c1,c2))
} = {
  mpd(p0, iff(eq(c0,c1),eq(c2,c3)), eq(c0,c3))
  syl(p0, imp(eq(c0,c3),iff(eq(c0,c1),eq(c2,c3))), eq(c1,c2))
  eq.iffeq.class(c0, c1, c2, c3)
}
```

```follow
thm eq.rw2.class(prop p0, class c0, class c1, class c2) {
  |- imp(p0, eq(c0, c1))
  -| imp(p0, eq(c2, c1))
  -| eq(c2, c0)
} = {
  mpi(p0, eq(c0,c1), eq(c2,c0))
  syl(p0, imp(eq(c2,c0),eq(c0,c1)), eq(c2,c1))
  eq.trans.class(c2, c1, c0)
}
```

```follow
thm eq.rw3.class(prop p0, class c0, class c1, class c2) {
  |- imp(p0, eq(c0, c1))
  -| imp(p0, eq(c0, c2))
  -| eq(c2, c1)
} = {
  mpi(p0, eq(c0,c1), eq(c2,c1))
  syl(p0, imp(eq(c2,c1),eq(c0,c1)), eq(c0,c2))
  eq.trans.class(c0, c2, c1)
}
```

```follow
thm eq.rw23.class(prop p0, class c0, class c1, class c2, class c3) {
  |- imp(p0, eq(c0, c1))
  -| imp(p0, eq(c2, c3))
  -| eq(c2, c0)
  -| eq(c3, c1)
} = {
  eq.rw2.class(p0, c0, c1, c2)
  eq.rw3.class(p0, c2, c1, c3)
}
```

```follow
thm in.subs.1(set s0, set s1, set s2) {
  |- iff(subs(in(c(s0),c(s2)), s0, s1), in(c(s1),c(s2)))
  |- iff(in(c(s1),c(s2)), subs(in(c(s0),c(s2)), s0, s1))
  |- imp(subs(in(c(s0),c(s2)), s0, s1), in(c(s1),c(s2)))
  |- imp(in(c(s1),c(s2)), subs(in(c(s0),c(s2)), s0, s1))
  diff (s0, s2)
} = {
  iff.comi(in(c(s1),c(s2)), subs(in(c(s0),c(s2)),s0,s1))
  iff.lefti(subs(in(c(s0),c(s2)),s0,s1), in(c(s1),c(s2)))
  iff.righti(in(c(s1),c(s2)), subs(in(c(s0),c(s2)),s0,s1))
  subs.special.diff.3(in(c(s0),c(s2)), s0, in(c(s1),c(s2)), s1, in(c(hs0),c(s2)), hs0)
  a8(s0, hs0, s2)
  a8(hs0, s1, s2)
}
```

```follow
thm cab.set(set s0, set s1) {
  |- eq(c(s0),cab(s1, in(c(s1),c(s0))))
  diff (s0, s1)
} = {
  eq.defigen(c(s0), cab(s1,in(c(s1),c(s0))), hs0)
  iff.syl(in(c(hs0),c(s0)), in(c(hs0),cab(s1,in(c(s1),c(s0)))), subs(in(c(s1),c(s0)),s1,hs0))
  cab.def.1.ext(hs0, s1, in(c(s1),c(s0)))
  in.subs.1(s1, hs0, s0)
}
```

# 定义 class 之间的包含关系

```follow
axiom in.def(class c0, class c1, set s0) {
  |- iff(in(c0,c1), exist(s0,and(eq(c(s0),c0), in(c(s0),c1))))
  diff (s0, c0) (s0, c1)
} 
```

```follow
thm in.def.ext(class c0, class c1, set s0) {
  |- iff(exist(s0,and(eq(c(s0),c0), in(c(s0),c1))), in(c0,c1))
  |- imp(in(c0,c1), exist(s0,and(eq(c(s0),c0), in(c(s0),c1))))
  |- imp(exist(s0,and(eq(c(s0),c0), in(c(s0),c1))), in(c0,c1))
  diff (s0, c0) (s0, c1)
} = {
  iff.comi(exist(s0,and(eq(c(s0),c0),in(c(s0),c1))), in(c0,c1))
  iff.lefti(in(c0,c1), exist(s0,and(eq(c(s0),c0),in(c(s0),c1))))
  iff.righti(exist(s0,and(eq(c(s0),c0),in(c(s0),c1))), in(c0,c1))
  in.def(c0, c1, s0)
}
```

```follow
thm in.defigen(class c0, class c1, set s0) {
  |- in(c0,c1) 
  -| and(eq(c(s0),c0), in(c(s0),c1))
  diff (s0, c0) (s0, c1)
} = {
  mp(in(c0,c1), exist(s0,and(eq(c(s0),c0),in(c(s0),c1))))
  in.def.ext(c0, c1, s0)
  gen.exist(s0, and(eq(c(s0),c0),in(c(s0),c1)))
}
```

```follow
thm in.defigend(class c0, class c1, set s0, prop p0) {
  |- imp(p0, in(c0,c1))
  -| imp(p0, and(eq(c(s0),c0), in(c(s0),c1)))
  diff (s0, c0) (s0, c1) (s0, p0)
} = {
  syl(p0, in(c0,c1), exist(s0,and(eq(c(s0),c0),in(c(s0),c1))))
  in.def.ext(c0, c1, s0)
  gend(s0, and(eq(c(s0),c0),in(c(s0),c1)), p0)
}
```

```follow
thm a8.class(class c0, class c1, class c2) {
  |- imp(eq(c0,c1), iff(in(c0, c2), in(c1, c2)))
  |- imp(eq(c0,c1), iff(in(c1, c2), in(c0, c2)))
  |- imp(eq(c0,c1), imp(in(c0, c2), in(c1, c2)))
  |- imp(eq(c0,c1), imp(in(c1, c2), in(c0, c2)))
} = {
  iff.comid(eq(c0,c1), in(c1,c2), in(c0,c2))
  iff.leftid(eq(c0,c1), in(c0,c2), in(c1,c2))
  iff.rightid(eq(c0,c1), in(c1,c2), in(c0,c2))
  iff.rw23(eq(c0,c1), in(c0,c2), in(c1,c2), exist(hs0,and(eq(c(hs0),c0),in(c(hs0),c2))), exist(hs0,and(eq(c(hs0),c1),in(c(hs0),c2))))
  in.def(c0, c2, hs0)
  in.def(c1, c2, hs0)
  a4id.aee.iff(hs0, and(eq(c(hs0),c0),in(c(hs0),c2)), and(eq(c(hs0),c1),in(c(hs0),c2)), eq(c0,c1))
  a4igen.diff.aaa.2(hs0, iff(and(eq(c(hs0),c0),in(c(hs0),c2)),and(eq(c(hs0),c1),in(c(hs0),c2))), eq(c0,c1))
  and.iffandiid.1(eq(c0,c1), eq(c(hs0),c0), eq(c(hs0),c1), in(c(hs0),c2), in(c(hs0),c2))
  iff.idd(eq(c0,c1), in(c(hs0),c2))
  eq.trans.class.iff.2(c0, c1, c(hs0))
}
```

```follow
thm a8i.class(class c0, class c1, class c2) {
  |- iff(in(c0, c2), in(c1, c2))
  |- iff(in(c1, c2), in(c0, c2))
  |- imp(in(c0, c2), in(c1, c2))
  |- imp(in(c1, c2), in(c0, c2))
  -| eq(c0,c1)
} = {
  mp(iff(in(c0,c2),in(c1,c2)), eq(c0,c1))
  mp(iff(in(c1,c2),in(c0,c2)), eq(c0,c1))
  mp(imp(in(c0,c2),in(c1,c2)), eq(c0,c1))
  mp(imp(in(c1,c2),in(c0,c2)), eq(c0,c1))
  a8.class(c0, c1, c2)
}
```

```follow
thm a8id.class(class c0, class c1, class c2, prop p0) {
  |- imp(p0, iff(in(c0, c2), in(c1, c2)))
  |- imp(p0, iff(in(c1, c2), in(c0, c2)))
  |- imp(p0, imp(in(c0, c2), in(c1, c2)))
  |- imp(p0, imp(in(c1, c2), in(c0, c2)))
  -| imp(p0, eq(c0,c1))
} = {
  syl(p0, iff(in(c0,c2),in(c1,c2)), eq(c0,c1))
  syl(p0, iff(in(c1,c2),in(c0,c2)), eq(c0,c1))
  syl(p0, imp(in(c0,c2),in(c1,c2)), eq(c0,c1))
  syl(p0, imp(in(c1,c2),in(c0,c2)), eq(c0,c1))
  a8.class(c0, c1, c2)
}
```

```follow
thm a8ii.class(class c0, class c1, class c2) {
  |- in(c0, c1)
  -| in(c2, c1)
  -| eq(c2, c0)
} = {
  mp(in(c0,c1), in(c2,c1))
  a8i.class(c2, c0, c1)

}
```

```follow
thm a8iid.class(class c0, class c1, class c2, prop p0) {
  |- imp(p0, in(c0, c1))
  -| imp(p0, in(c2, c1))
  -| imp(p0, eq(c2, c0))
} = {
  mpd(p0, in(c0,c1), in(c2,c1))
  a8id.class(c2, c0, c1, p0)
}
```

```follow
thm a8iid.not.class(class c0, class c1, class c2, prop p0) {
  |- imp(p0, not(in(c0, c1)))
  -| imp(p0, not(in(c2, c1)))
  -| imp(p0, eq(c2, c0))
} = {
  mpd(p0, not(in(c0,c1)), not(in(c2,c1)))
  syl(p0, imp(not(in(c2,c1)),not(in(c0,c1))), eq(c2,c0))
  conid.4(eq(c2,c0), in(c2,c1), in(c0,c1))
  a8.class(c2, c0, c1)
}
```

```follow
thm a9.class(class c0, class c1, class c2) {
  |- imp(eq(c0,c1), iff(in(c2, c0), in(c2, c1)))
  |- imp(eq(c0,c1), iff(in(c2, c1), in(c2, c0)))
  |- imp(eq(c0,c1), imp(in(c2, c0), in(c2, c1)))
  |- imp(eq(c0,c1), imp(in(c2, c1), in(c2, c0)))
} = {
  iff.comid(eq(c0,c1), in(c2,c1), in(c2,c0))
  iff.leftid(eq(c0,c1), in(c2,c0), in(c2,c1))
  iff.rightid(eq(c0,c1), in(c2,c1), in(c2,c0))
  iff.rw23(eq(c0,c1), in(c2,c0), in(c2,c1), exist(hs0,and(eq(c(hs0),c2),in(c(hs0),c0))), exist(hs0,and(eq(c(hs0),c2),in(c(hs0),c1))))
  in.def(c2, c0, hs0)
  in.def(c2, c1, hs0)
  syl(eq(c0,c1), iff(exist(hs0,and(eq(c(hs0),c2),in(c(hs0),c0))),exist(hs0,and(eq(c(hs0),c2),in(c(hs0),c1)))), forall(hs0,iff(in(c(hs0),c0),in(c(hs0),c1))))
  eq.def.ext(c0, c1, hs0)
  a4id.aee.iff(hs0, and(eq(c(hs0),c2),in(c(hs0),c0)), and(eq(c(hs0),c2),in(c(hs0),c1)), forall(hs0,iff(in(c(hs0),c0),in(c(hs0),c1))))
  a4igen.aaa(hs0, iff(in(c(hs0),c0),in(c(hs0),c1)), iff(and(eq(c(hs0),c2),in(c(hs0),c0)),and(eq(c(hs0),c2),in(c(hs0),c1))))
  mpi(iff(in(c(hs0),c0),in(c(hs0),c1)), iff(and(eq(c(hs0),c2),in(c(hs0),c0)),and(eq(c(hs0),c2),in(c(hs0),c1))), iff(eq(c(hs0),c2),eq(c(hs0),c2)))
  and.iffand.1(eq(c(hs0),c2), eq(c(hs0),c2), in(c(hs0),c0), in(c(hs0),c1))
  iff.id(eq(c(hs0),c2))
}
```

```follow
thm a9i.class(class c0, class c1, class c2) {
  |- iff(in(c2, c0), in(c2, c1))
  |- iff(in(c2, c1), in(c2, c0))
  |- imp(in(c2, c0), in(c2, c1))
  |- imp(in(c2, c1), in(c2, c0))
  -| eq(c0,c1)
} = {
  mp(iff(in(c2,c0),in(c2,c1)), eq(c0,c1))
  mp(iff(in(c2,c1),in(c2,c0)), eq(c0,c1))
  mp(imp(in(c2,c0),in(c2,c1)), eq(c0,c1))
  mp(imp(in(c2,c1),in(c2,c0)), eq(c0,c1))
  a9.class(c0, c1, c2)
}
```

```follow
thm a9id.class(class c0, class c1, class c2, prop p0) {
  |- imp(p0, iff(in(c2, c0), in(c2, c1)))
  |- imp(p0, iff(in(c2, c1), in(c2, c0)))
  |- imp(p0, imp(in(c2, c0), in(c2, c1)))
  |- imp(p0, imp(in(c2, c1), in(c2, c0)))
  -| imp(p0, eq(c0,c1))
} = {
  syl(p0, iff(in(c2,c0),in(c2,c1)), eq(c0,c1))
  syl(p0, imp(in(c2,c0),in(c2,c1)), eq(c0,c1))
  syl(p0, imp(in(c2,c1),in(c2,c0)), eq(c0,c1))
  syl(p0, iff(in(c2,c1),in(c2,c0)), eq(c0,c1))
  a9.class(c0, c1, c2)
}
```

```follow
thm a9ii.class(class c0, class c1, class c2) {
  |- in(c0, c1)
  -| in(c0, c2)
  -| eq(c2, c1)
} = {
  mp(in(c0,c1), in(c0,c2))
  a9i.class(c2, c1, c0)
}
```

```follow
thm a9iid.class(class c0, class c1, class c2, prop p0) {
  |- imp(p0, in(c0, c1))
  -| imp(p0, in(c0, c2))
  -| imp(p0, eq(c2, c1))
} = {
  mpd(p0, in(c0,c1), in(c0,c2))
  a9id.class(c2, c1, c0, p0)
}
```

```follow
thm a9iid.not.class(class c0, class c1, class c2, prop p0) {
  |- imp(p0, not(in(c0, c1)))
  -| imp(p0, not(in(c0, c2)))
  -| imp(p0, eq(c2, c1))
} = {
  mpd(p0, not(in(c0,c1)), not(in(c0,c2)))
  syl(p0, imp(not(in(c0,c2)),not(in(c0,c1))), eq(c2,c1))
  conid.4(eq(c2,c1), in(c0,c2), in(c0,c1))
  a9.class(c2, c1, c0)
}
```


```follow
thm in.iffin(class c0, class c1, class c2, class c3) {
  |- imp(and(eq(c0,c2),eq(c1,c3)), iff(in(c0,c1),in(c2,c3)))
  |- imp(eq(c0,c2),imp(eq(c1,c3), iff(in(c0,c1),in(c2,c3))))
  |- imp(and(eq(c1,c3),eq(c0,c2)), iff(in(c0,c1),in(c2,c3)))
  |- imp(eq(c1,c3),imp(eq(c0,c2), iff(in(c0,c1),in(c2,c3))))
} = {
  and.joini(eq(c1,c3), eq(c0,c2), iff(in(c0,c1),in(c2,c3)))
  com12i(eq(c1,c3), eq(c0,c2), iff(in(c0,c1),in(c2,c3)))
  and.spliti(eq(c0,c2), eq(c1,c3), iff(in(c0,c1),in(c2,c3)))
  iff.and.syl(eq(c0,c2), eq(c1,c3), in(c0,c1), in(c2,c3), in(c2,c1))
  a8.class(c0, c2, c1)
  a9.class(c1, c3, c2)
}
```

```follow
thm in.iffinii(class c0, class c1, class c2, class c3) {
  |- iff(in(c0,c1),in(c2,c3))
  -| eq(c0,c2)
  -| eq(c1,c3)
} = {
  mp(iff(in(c0,c1),in(c2,c3)), eq(c0,c2))
  mp(imp(eq(c0,c2),iff(in(c0,c1),in(c2,c3))), eq(c1,c3))
  in.iffin(c0, c1, c2, c3)
}
```

```follow
thm in.iffiniid(class c0, class c1, class c2, class c3, prop p0) {
  |- imp(p0, iff(in(c0,c1),in(c2,c3)))
  -| imp(p0, eq(c0,c2))
  -| imp(p0, eq(c1,c3))
} = {
  mpd(p0, iff(in(c0,c1),in(c2,c3)), eq(c0,c2))
  syl(p0, imp(eq(c0,c2),iff(in(c0,c1),in(c2,c3))), eq(c1,c3))
  in.iffin(c0, c1, c2, c3)
}
```

```follow
thm neq.class.1(class c0, class c1, class c2) {
  |- imp(and(in(c0,c2),not(in(c1,c2))), not(eq(c0,c1)))
} = {
  and.joini(in(c0,c2), not(in(c1,c2)), not(eq(c0,c1)))
  conid.4(in(c0,c2), in(c1,c2), eq(c0,c1))
  com12i(in(c0,c2), eq(c0,c1), in(c1,c2))
  a8.class(c0, c1, c2)
}
```

```follow
thm neq.class.2(class c0, class c1, class c2) {
  |- imp(and(in(c0,c1),not(in(c0,c2))), not(eq(c1,c2)))
} = {
  and.joini(in(c0,c1), not(in(c0,c2)), not(eq(c1,c2)))
  conid.4(in(c0,c1), in(c0,c2), eq(c1,c2))
  com12i(in(c0,c1), eq(c1,c2), in(c0,c2))
  a9.class(c1, c2, c0)
}
```

## Subs

```follow
thm eq.subs.class(class c0, set s0, set s1) {
  |- iff(subs(eq(c(s0), c0), s0, s1), eq(c(s1),c0))
  |- iff(eq(c(s1),c0), subs(eq(c(s0), c0), s0, s1))
  |- imp(subs(eq(c(s0), c0), s0, s1), eq(c(s1),c0))
  |- imp(eq(c(s1),c0), subs(eq(c(s0), c0), s0, s1))
  diff (s0, c0)
} = {
  iff.comi(eq(c(s1),c0), subs(eq(c(s0),c0),s0,s1))
  iff.lefti(subs(eq(c(s0),c0),s0,s1), eq(c(s1),c0))
  iff.righti(eq(c(s1),c0), subs(eq(c(s0),c0),s0,s1))
  subs.special.diff.3(eq(c(s0),c0), s0, eq(c(s1),c0), s1, eq(c(hs0),c0), hs0)
  eq.trans.class.iff.1(c(s0), c(hs0), c0)
  eq.trans.class.iff.1(c(hs0), c(s1), c0)
}
```

```follow
thm in.subs.class(class c0, set s0, set s1) {
  |- iff(subs(in(c(s0), c0), s0, s1), in(c(s1),c0))
  |- iff(in(c(s1),c0), subs(in(c(s0), c0), s0, s1))
  |- imp(subs(in(c(s0), c0), s0, s1), in(c(s1),c0))
  |- imp(in(c(s1),c0), subs(in(c(s0), c0), s0, s1))
  diff (s0, c0)
} = {
  iff.comi(in(c(s1),c0), subs(in(c(s0),c0),s0,s1))
  iff.lefti(in(c(s1),c0), subs(in(c(s0),c0),s0,s1))
  iff.righti(subs(in(c(s0),c0),s0,s1), in(c(s1),c0))
  subs.special.diff.3(in(c(s0),c0), s0, in(c(s1),c0), s1, in(c(hs0),c0), hs0)
  a8.class(c(s0), c(hs0), c0)
  a8.class(c(hs0), c(s1), c0)
}
```

```follow
thm in.a5.rw.1(set s0, set s1, class c0, class c1) {
  |- imp(in(c(s0),c0),forall(s1,in(c(s0),c0)))
  -| imp(in(c(s0),c1),forall(s1,in(c(s0),c1)))
  -| eq(c0, c1)
} = {
  a5.rw(s1, in(c(s0),c0), in(c(s0),c1))
  a9i.class(c0, c1, c(s0))
}
```

```follow
thm in.a5.rw.2(set s0, set s1, set s2, class c0) {
  |- imp(in(c(s0),c0),forall(s1,in(c(s0),c0)))
  -| imp(in(c(s2),c0),forall(s1,in(c(s2),c0)))
  diff (s0, s1) (s2, c0)
} = {
  syl(in(c(s0),c0), forall(s1,in(c(s0),c0)), subs(in(c(s2),c0),s2,s0))
  in.subs.class(c0, s2, s0)
  syl(subs(in(c(s2),c0),s2,s0), forall(s1,in(c(s0),c0)), forall(s1,subs(in(c(s2),c0),s2,s0)))
  a4igen.aaa(s1, subs(in(c(s2),c0),s2,s0), in(c(s0),c0))
  in.subs.class(c0, s2, s0)
  subs.forallsubs(in(c(s2),c0), s2, s0, s1)
}
```

## 等价定义 

```follow
thm cab.eq.forall.lemma(class c0, class c1, set s0, set s1) {
  |- iff(eq(c0,c1), forall(s0,iff(in(c(s0),c0), in(c(s0),c1))))
  |- iff(forall(s0,iff(in(c(s0),c0), in(c(s0),c1))), eq(c0,c1))
  -| imp(in(c(s1),c0), forall(s0, in(c(s1), c0)))
  -| imp(in(c(s1),c1), forall(s0, in(c(s1), c1)))
  diff (s1, s0) (s1, c0) (s1, c1)
} = {
  iff.comi(forall(s0,iff(in(c(s0),c0),in(c(s0),c1))), eq(c0,c1))
  iff.syl(eq(c0,c1), forall(s0,iff(in(c(s0),c0),in(c(s0),c1))), forall(s1,iff(in(c(s1),c0),in(c(s1),c1))))
  eq.def(c0, c1, s1)
  nf.eq.forall.iff.1(s1, s0, iff(in(c(s1),c0),in(c(s1),c1)), iff(in(c(s0),c0),in(c(s0),c1)))
  nf.diff(s1, iff(in(c(s0),c0),in(c(s0),c1)))
  nf.iffii(s0, in(c(s1),c0), in(c(s1),c1))
  nf.introigen.2(s0, in(c(s1),c0))
  nf.introigen.2(s0, in(c(s1),c1))
  iff.introiid.1(eq(c(s1),c(s0)), iff(in(c(s1),c0),in(c(s1),c1)), iff(in(c(s0),c0),in(c(s0),c1)))
  iff.2iffiid.2(in(c(s1),c0), in(c(s1),c1), in(c(s0),c0), in(c(s0),c1), eq(c(s1),c(s0)))
  iff.2iffiid.2(in(c(s0),c0), in(c(s0),c1), in(c(s1),c0), in(c(s1),c1), eq(c(s1),c(s0)))
  a8.class(c(s1), c(s0), c0)
  a8.class(c(s1), c(s0), c1)
}
```


```follow 
thm cab.eq.forall.1(set s0, class c0, prop p0) {
  |- iff(eq(c0, cab(s0, p0)), forall(s0, iff(in(c(s0),c0), p0)))
  diff (s0, c0)
} = {
  iff.syl(eq(c0,cab(s0,p0)), forall(s0,iff(in(c(s0),c0),p0)), forall(s0,iff(in(c(s0),c0),in(c(s0),cab(s0,p0)))))
  cab.eq.forall.lemma(c0, cab(s0,p0), s0, hs0)
  a5.forall.1(s0, in(c(hs0),c0))
  nf.a5(in(c(hs0),cab(s0,p0)), s0)
  cab.nf.1(p0, s0, hs0)
  a4igen.aaa.iff(s0, iff(in(c(s0),c0),in(c(s0),cab(s0,p0))), iff(in(c(s0),c0),p0))
  iff.introii.1(iff(in(c(s0),c0),in(c(s0),cab(s0,p0))), iff(in(c(s0),c0),p0))
  iff.transi.1(p0, in(c(s0),cab(s0,p0)), in(c(s0),c0))
  cab.id(p0, s0)
}
```

```follow 
thm cab.eq.forall.2(set s0, class c0, prop p0) {
  |- iff(eq(cab(s0, p0), c0), forall(s0, iff(in(c(s0),c0), p0)))
  |- iff(eq(c0, cab(s0, p0)), forall(s0, iff(p0, in(c(s0),c0))))
  |- iff(eq(cab(s0, p0), c0), forall(s0, iff(p0, in(c(s0),c0))))
  diff (s0, c0)
} = {
  iff.syl(eq(cab(s0,p0),c0), forall(s0,iff(in(c(s0),c0),p0)), eq(c0,cab(s0,p0)))
  eq.com.class.iff(cab(s0,p0), c0)
  cab.eq.forall.1(s0, c0, p0)
  iff.syl(eq(cab(s0,p0),c0), forall(s0,iff(p0,in(c(s0),c0))), eq(c0,cab(s0,p0)))
  eq.com.class.iff(cab(s0,p0), c0)
  iff.syl(eq(c0,cab(s0,p0)), forall(s0,iff(p0,in(c(s0),c0))), forall(s0,iff(in(c(s0),c0),p0)))
  cab.eq.forall.1(s0, c0, p0)
  a4igen.aaa.iff(s0, iff(in(c(s0),c0),p0), iff(p0,in(c(s0),c0)))
  iff.com(in(c(s0),c0), p0)
}
```

```follow 
thm cab.eq.foralli.1(set s0, class c0, prop p0) {
  |- forall(s0, iff(in(c(s0),c0), p0))
  -| eq(c0, cab(s0, p0))
  diff (s0, c0)
} = {
  mp(forall(s0,iff(in(c(s0),c0),p0)), eq(c0,cab(s0,p0)))
  iff.lefti(eq(c0,cab(s0,p0)), forall(s0,iff(in(c(s0),c0),p0)))
  cab.eq.forall.1(s0, c0, p0)
}
```

```follow 
thm cab.eq.forallid.1(set s0, class c0, prop p0, prop p1) {
  |- imp(p1, forall(s0, iff(in(c(s0),c0), p0)))
  -| imp(p1, eq(c0, cab(s0, p0)))
  diff (s0, c0)
} = {
  syl(p1, forall(s0,iff(in(c(s0),c0),p0)), eq(c0,cab(s0,p0)))
  iff.lefti(eq(c0,cab(s0,p0)), forall(s0,iff(in(c(s0),c0),p0)))
  cab.eq.forall.1(s0, c0, p0)
}
```

```follow 
thm cab.eq.forallspi.1(set s0, class c0, prop p0) {
  |- iff(in(c(s0),c0), p0)
  -| eq(c0, cab(s0, p0))
  diff (s0, c0)
} = {
  mp(iff(in(c(s0),c0),p0), forall(s0,iff(in(c(s0),c0),p0)))
  special.2(iff(in(c(s0),c0),p0), s0)
  cab.eq.foralli.1(s0, c0, p0)
}
```

```follow 
thm cab.eq.forallspid.1(set s0, class c0, prop p0, prop p1) {
  |- imp(p1, iff(in(c(s0),c0), p0))
  -| imp(p1, eq(c0, cab(s0, p0)))
  diff (s0, c0)
} = {
  syl(p1, iff(in(c(s0),c0),p0), forall(s0,iff(in(c(s0),c0),p0)))
  special.2(iff(in(c(s0),c0),p0), s0)
  cab.eq.forallid.1(s0, c0, p0, p1)
}
```

```follow 
thm cab.eq.foralli.2(set s0, class c0, prop p0) {
  |- eq(c0, cab(s0, p0))
  -| forall(s0, iff(in(c(s0),c0), p0))
  diff (s0, c0)
} = {
  mp(eq(c0,cab(s0,p0)), forall(s0,iff(in(c(s0),c0),p0)))
  iff.righti(forall(s0,iff(in(c(s0),c0),p0)), eq(c0,cab(s0,p0)))
  cab.eq.forall.1(s0, c0, p0)
}
```

```follow 
thm cab.eq.forallid.2(set s0, class c0, prop p0, prop p1) {
  |- imp(p1, eq(c0, cab(s0, p0)))
  -| imp(p1, forall(s0, iff(in(c(s0),c0), p0)))
  diff (s0, c0)
} = {
  syl(p1, eq(c0,cab(s0,p0)), forall(s0,iff(in(c(s0),c0),p0)))
  iff.righti(forall(s0,iff(in(c(s0),c0),p0)), eq(c0,cab(s0,p0)))
  cab.eq.forall.1(s0, c0, p0)
}
```

```follow 
thm cab.eq.foralligen.2(set s0, class c0, prop p0) {
  |- eq(c0, cab(s0, p0))
  -| iff(in(c(s0),c0), p0)
  diff (s0, c0)
} = {
  cab.eq.foralli.2(s0, c0, p0)
  gen.forall(s0, iff(in(c(s0),c0),p0))
}
```

```follow 
thm cab.eq.foralligend.2(set s0, class c0, prop p0, prop p1) {
  |- imp(p1, eq(c0, cab(s0, p0)))
  -| imp(p1, iff(in(c(s0),c0), p0))
  diff (s0, c0) (s0, p1)
} = {
  cab.eq.forallid.2(s0, c0, p0, p1)
  a4igen.diff.aaa.2(s0, iff(in(c(s0),c0),p0), p1)
}
```

## `cab.eqcab` 

```follow
thm cab.eqcab(set s0, prop p0, prop p1) {
  |- iff(forall(s0, iff(p0, p1)), eq(cab(s0,p0), cab(s0,p1)))
} = {
  iff.syl(forall(s0,iff(p0,p1)), eq(cab(s0,p0),cab(s0,p1)), forall(s0,iff(in(c(s0),cab(s0,p0)),in(c(s0),cab(s0,p1)))))
  cab.eq.forall.lemma(cab(s0,p0), cab(s0,p1), s0, hs0)
  nf.a5(in(c(hs0),cab(s0,p0)), s0)
  cab.nf.1(p0, s0, hs0)
  nf.a5(in(c(hs0),cab(s0,p1)), s0)
  cab.nf.1(p1, s0, hs0)
  a4igen.aaa.iff(s0, iff(p0,p1), iff(in(c(s0),cab(s0,p0)),in(c(s0),cab(s0,p1))))
  iff.iffiffii(p0, p1, in(c(s0),cab(s0,p0)), in(c(s0),cab(s0,p1)))
  cab.id(p0, s0)
  cab.id(p1, s0)
}
```

```follow
thm cab.eqcabi.1(set s0, prop p0, prop p1) {
  |- eq(cab(s0,p0), cab(s0,p1))
  -| forall(s0, iff(p0, p1)) 
} = {
  mp(eq(cab(s0,p0),cab(s0,p1)), forall(s0,iff(p0,p1)))
  iff.lefti(forall(s0,iff(p0,p1)), eq(cab(s0,p0),cab(s0,p1)))
  cab.eqcab(s0, p0, p1)
}
```

```follow
thm cab.eqcabid.1(set s0, prop p0, prop p1, prop p2) {
  |- imp(p2, eq(cab(s0,p0), cab(s0,p1)))
  -| imp(p2, forall(s0, iff(p0, p1)))
} = {
  syl(p2, eq(cab(s0,p0),cab(s0,p1)), forall(s0,iff(p0,p1)))
  iff.lefti(forall(s0,iff(p0,p1)), eq(cab(s0,p0),cab(s0,p1)))
  cab.eqcab(s0, p0, p1)
}
```

```follow
thm cab.eqcabigen.1(set s0, prop p0, prop p1) {
  |- eq(cab(s0,p0), cab(s0,p1))
  -| iff(p0, p1)
} = {
  cab.eqcabi.1(s0, p0, p1)
  gen.forall(s0, iff(p0,p1))
}
```

```follow
thm cab.eqcabigend.1(set s0, prop p0, prop p1, prop p2) {
  |- imp(p2, eq(cab(s0,p0), cab(s0,p1)))
  -| imp(p2, iff(p0, p1))
  -| nf(s0, p2)
} = {
  cab.eqcabid.1(s0, p0, p1, p2)
  nf.gend(s0, iff(p0,p1), p2)
}
```

```follow
thm cab.eqcabi.2(set s0, prop p0, prop p1) {
  |- forall(s0, iff(p0, p1)) 
  -| eq(cab(s0,p0), cab(s0,p1))
} = {
  mp(forall(s0,iff(p0,p1)), eq(cab(s0,p0),cab(s0,p1)))
  iff.righti(eq(cab(s0,p0),cab(s0,p1)), forall(s0,iff(p0,p1)))
  cab.eqcab(s0, p0, p1)
}
```

```follow
thm cab.eqcabid.2(set s0, prop p0, prop p1, prop p2) {
  |- imp(p2, forall(s0, iff(p0, p1)))
  -| imp(p2, eq(cab(s0,p0), cab(s0,p1)))
} = {
  syl(p2, forall(s0,iff(p0,p1)), eq(cab(s0,p0),cab(s0,p1)))
  iff.righti(eq(cab(s0,p0),cab(s0,p1)), forall(s0,iff(p0,p1)))
  cab.eqcab(s0, p0, p1)
}

```follow
thm cab.eqcabspi.2(set s0, prop p0, prop p1) {
  |- iff(p0, p1)
  -| eq(cab(s0,p0), cab(s0,p1))
} = {
  mp(iff(p0,p1), forall(s0,iff(p0,p1)))
  special.2(iff(p0,p1), s0)
  cab.eqcabi.2(s0, p0, p1)
}
```

```follow
thm cab.eqcabspid.2(set s0, prop p0, prop p1, prop p2) {
  |- imp(p2, iff(p0, p1))
  -| imp(p2, eq(cab(s0,p0), cab(s0,p1)))
} = {
  syl(p2, iff(p0,p1), forall(s0,iff(p0,p1)))
  special.2(iff(p0,p1), s0)
  cab.eqcabid.2(s0, p0, p1, p2)
}
```

```follow
thm cab.eqcabspid.subs(set s0, set s1, prop p0, prop p1, prop p2) {
  |- imp(p2, eq(cab(s0,p0), cab(s0,p1)))
  -| imp(p2, iff(subs(p0,s0,s1), subs(p1,s0,s1)))
  diff (s1, s0) (s1, p0) (s1, p1) (s1, p2)
} = {
  eq.defigend(cab(s0,p0), cab(s0,p1), s1, p2)
  iff.rw23(p2, in(c(s1),cab(s0,p0)), in(c(s1),cab(s0,p1)), subs(p0,s0,s1), subs(p1,s0,s1))
  cab.def.1(s1, s0, p0)
  cab.def.1(s1, s0, p1)
}
```

```follow
thm cab.id.class(class c0, set s0) {
  |- eq(c0, cab(s0, in(c(s0), c0)))
  |- eq(cab(s0, in(c(s0), c0)), c0)
  diff (c0, s0)
} = {
  eq.comi.class(cab(s0,in(c(s0),c0)), c0)
  cab.eq.foralligen.2(s0, c0, in(c(s0),c0))
  iff.id(in(c(s0),c0))
}
```

```follow
thm cab.eqcab.3(set s0, prop p0, set s1, prop p1) {
  |- eq(cab(s0,p0), cab(s1,p1))
  -| imp(eq(c(s0),c(s1)), iff(p0,p1))
  diff (s0,s1) (s0,p1) (s1,p0)
} = {
  eq.defigen(cab(s0,p0), cab(s1,p1), hs0)
  iff.syl(in(c(hs0),cab(s0,p0)), in(c(hs0),cab(s1,p1)), subs(p0,s0,hs0))
  cab.def.1(hs0, s0, p0)
  iff.syl(subs(p0,s0,hs0), in(c(hs0),cab(s1,p1)), subs(p1,s1,hs0))
  cab.def.1.ext(hs0, s1, p1)
  iff.syl(subs(p0,s0,hs0), subs(p1,s1,hs0), subs(subs(p0,s0,s1),s1,hs0))
  subs.trans.diff(p0, s0, s1, hs0)
  subs.iffsubsigen(subs(p0,s0,s1), p1, s1, hs0)
  subs.special.diff.2(p0, s0, p1, s1)
}
```

```follow
thm cab.eqcab.4(set s0, prop p0, set s1, prop p1) {
  |- eq(cab(s0,p0),cab(s1,p1))
  -| imp(eq(c(s0),c(s1)), iff(p0,p1))
  -| nf(s1, p0)
  -| nf(s0, p1)
} = {
  eq.defigen(cab(s0,p0), cab(s1,p1), hs0)
  iff.syl(in(c(hs0),cab(s0,p0)), in(c(hs0),cab(s1,p1)), subs(p0,s0,hs0))
  cab.def.1(hs0, s0, p0)
  iff.syl(subs(p0,s0,hs0), in(c(hs0),cab(s1,p1)), subs(p1,s1,hs0))
  cab.def.1.ext(hs0, s1, p1)
  iff.syl(subs(p0,s0,hs0), subs(p1,s1,hs0), subs(subs(p0,s0,s1),s1,hs0))
  nf.subs.trans(s0, hs0, s1, p0)
  subs.iffsubsigen(subs(p0,s0,s1), p1, s1, hs0)
  nf.subs.a5(s0, s1, p0, p1)
}
```

```follow
thm cab.exist(class c0, set s0, prop p0) {
  |- iff(in(c0, cab(s0, p0)), exist(s0, and(eq(c(s0),c0), p0)))
  diff (s0, c0)
} = {
  iff.syl(in(c0,cab(s0,p0)), exist(s0,and(eq(c(s0),c0),p0)), exist(hs0,and(eq(c(hs0),c0),in(c(hs0),cab(s0,p0)))))
  in.def(c0, cab(s0,p0), hs0)
  nf.eq.exist.iff.1(hs0, s0, and(eq(c(hs0),c0),in(c(hs0),cab(s0,p0))), and(eq(c(s0),c0),p0))
  nf.diff(hs0, and(eq(c(s0),c0),p0))
  nf.andii(s0, eq(c(hs0),c0), in(c(hs0),cab(s0,p0)))
  nf.diff(s0, eq(c(hs0),c0))
  cab.nf.1(p0, s0, hs0)
  and.iffandiid.1(eq(c(hs0),c(s0)), eq(c(hs0),c0), eq(c(s0),c0), in(c(hs0),cab(s0,p0)), p0)
  eq.trans.class.iff.1(c(hs0), c(s0), c0)
  iff.rw2(eq(c(hs0),c(s0)), in(c(hs0),cab(s0,p0)), p0, subs(p0,s0,hs0))
  cab.def.1(hs0, s0, p0)
  subs.eq.5(p0, hs0, s0)
}
```

```follow
thm cab.inclass(set s0, prop p0, class c0, set s1) {
  |- iff(in(cab(s0,p0),c0), exist(s1, and(in(c(s1),c0), forall(s0, iff(in(c(s0),c(s1)), p0)))))
  diff (s1, s0) (s1, p0) (s1, c0)
} = {
  iff.syl(in(cab(s0,p0),c0), exist(s1,and(in(c(s1),c0),forall(s0,iff(in(c(s0),c(s1)),p0)))), exist(s1,and(eq(c(s1),cab(s0,p0)),in(c(s1),c0))))
  in.def(cab(s0,p0), c0, s1)
  a4igen.aee.iff(s1, and(eq(c(s1),cab(s0,p0)),in(c(s1),c0)), and(in(c(s1),c0),forall(s0,iff(in(c(s0),c(s1)),p0))))
  iff.syl(and(eq(c(s1),cab(s0,p0)),in(c(s1),c0)), and(in(c(s1),c0),forall(s0,iff(in(c(s0),c(s1)),p0))), and(in(c(s1),c0),eq(c(s1),cab(s0,p0))))
  iff.and.com(eq(c(s1),cab(s0,p0)), in(c(s1),c0))
  and.iffandii.1(in(c(s1),c0), in(c(s1),c0), eq(c(s1),cab(s0,p0)), forall(s0,iff(in(c(s0),c(s1)),p0)))
  iff.id(in(c(s1),c0))
  cab.eq.forall.1(s0, c(s1), p0)
}
```

```follow
thm cab.usesubs(set s0, set s1, class c0, set s2) {
  |- imp(eq(c(s0),c(s1)), eq(c0, cab(s2, subs(in(c(s2), c0), s0, s1))))
  diff (s2, s0) (s2, s1) (s2, c0)
} = {
  cab.eq.foralligend.2(s2, c0, subs(in(c(s2),c0),s0,s1), eq(c(s0),c(s1)))
  subs.eq.5(in(c(s2),c0), s0, s1)
}
```
