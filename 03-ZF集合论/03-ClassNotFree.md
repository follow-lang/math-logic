
# Class Not Free

`class` 版本的 `Not Free` 操作。这个章节的定理还好不多。

```follow
term prop nfc(set s0, class c0) { ㎋ᶜ(s0, c0) }
```

```follow
axiom nfc.def(set s0, class c0, set s1) {
  |- iff(nfc(s0,c0), forall(s1, nf(s0,in(c(s1), c0))))
  diff (s1, s0) (s1, c0)
}
```

```follow
thm nfc.def.rw(set s0, class c0, set s1, set s2) {
  |- iff(forall(s1,nf(s0,in(c(s1),c0))), forall(s2,nf(s0,in(c(s2),c0))))
  diff (s1, s2, s0) (s1, s2, c0)
} = {
  eq.forall.6(nf(s0,in(c(s1),c0)), s1, nf(s0,in(c(s2),c0)), s2)
  nf.iffnfid(s0, in(c(s1),c0), in(c(s2),c0), eq(c(s1),c(s2)))
  a4igen.diff.aaa.2(s0, iff(in(c(s1),c0),in(c(s2),c0)), eq(c(s1),c(s2)))
  a8.class(c(s1), c(s2), c0)
}
```

```follow
thm nfc.def.ext(set s0, class c0, set s1) {
  |- iff(nfc(s0,c0), forall(s1, nf(s0,in(c(s1), c0))))
  |- iff(forall(s1, nf(s0,in(c(s1), c0))), nfc(s0,c0))
  |- imp(nfc(s0,c0), forall(s1, nf(s0,in(c(s1), c0))))
  |- imp(forall(s1, nf(s0,in(c(s1), c0))), nfc(s0,c0))
  diff (s1, s0) (s1, c0)
} = {
  iff.comi(forall(s1,nf(s0,in(c(s1),c0))), nfc(s0,c0))
  iff.lefti(nfc(s0,c0), forall(s1,nf(s0,in(c(s1),c0))))
  iff.righti(forall(s1,nf(s0,in(c(s1),c0))), nfc(s0,c0))
  nfc.def(s0, c0, s1)
}
```

```follow
thm nfc.defi.1(set s0, class c0, set s1) {
  |- forall(s1, nf(s0,in(c(s1), c0)))
  -| nfc(s0,c0)
  diff (s1, s0) (s1, c0)
} = {
  mp(forall(s1,nf(s0,in(c(s1),c0))), nfc(s0,c0))
  nfc.def.ext(s0, c0, s1)
}
```

```follow
thm nfc.defid.1(set s0, class c0, set s1, prop p0) {
  |- imp(p0, forall(s1, nf(s0,in(c(s1), c0))))
  -| imp(p0, nfc(s0,c0))
  diff (s1, s0) (s1, c0)
} = {
  syl(p0, forall(s1,nf(s0,in(c(s1),c0))), nfc(s0,c0))
  nfc.def.ext(s0, c0, s1)
}
```

```follow
thm nfc.defspi.1(set s0, class c0, set s1) {
  |- nf(s0,in(c(s1),c0))
  -| nfc(s0,c0)
  diff (s1, s0) (s1, c0)
} = {
  mp(nf(s0,in(c(s1),c0)), forall(s1,nf(s0,in(c(s1),c0))))
  special.2(nf(s0,in(c(s1),c0)), s1)
  nfc.defi.1(s0, c0, s1)
}
```

```follow
thm nfc.defspid.1(set s0, class c0, set s1, prop p0) {
  |- imp(p0, nf(s0,in(c(s1),c0)))
  -| imp(p0, nfc(s0,c0))
  diff (s1, s0) (s1, c0) (s1, p0)
} = {
  syl(p0, nf(s0,in(c(s1),c0)), forall(s1,nf(s0,in(c(s1),c0))))
  nfc.defid.1(s0, c0, s1, p0)
  special.2(nf(s0,in(c(s1),c0)), s1)
}
```

```follow
thm nfc.defi.2(set s0, class c0, set s1) {
  |- nfc(s0,c0)
  -| forall(s1, nf(s0,in(c(s1), c0)))
  diff (s1, s0) (s1, c0)
} = {
  mp(nfc(s0,c0), forall(s1,nf(s0,in(c(s1),c0))))
  nfc.def.ext(s0, c0, s1)
}
```

```follow
thm nfc.defid.2(set s0, class c0, set s1, prop p0) {
  |- imp(p0, nfc(s0,c0))
  -| imp(p0, forall(s1, nf(s0,in(c(s1), c0))))
  diff (s1, s0) (s1, c0)
} = {
  syl(p0, nfc(s0,c0), forall(s1,nf(s0,in(c(s1),c0))))
  nfc.def.ext(s0, c0, s1)
}
```

```follow
thm nfc.defigen.2(set s0, class c0, set s1) {
  |- nfc(s0,c0)
  -| nf(s0,in(c(s1),c0))
  diff (s1, s0) (s1, c0)
} = {
  nfc.defi.2(s0, c0, s1)
  gen.forall(s1, nf(s0,in(c(s1),c0)))
}
```

```follow
thm nfc.defspid.2(set s0, class c0, set s1, prop p0) {
  |- imp(p0, nfc(s0,c0))
  -| imp(p0, nf(s0,in(c(s1),c0)))
  diff (s1, s0) (s1, c0) (s1, p0)
} = {
  nfc.defid.2(s0, c0, s1, p0)
  a4igen.diff.aaa.2(s1, nf(s0,in(c(s1),c0)), p0)
}
```

## `nfc.iffnfc` 

```follow
thm nfc.iffnfc.1(set s0, class c0, class c1) {
  |- imp(forall(s0, eq(c0,c1)), iff(nfc(s0,c0),nfc(s0,c1)))
} = {
  iff.rw23(forall(s0,eq(c0,c1)), nfc(s0,c0), nfc(s0,c1), forall(hs0,nf(s0,in(c(hs0),c0))), forall(hs0,nf(s0,in(c(hs0),c1))))
  nfc.def(s0, c0, hs0)
  nfc.def(s0, c1, hs0)
  a4id.aaa.iff(hs0, nf(s0,in(c(hs0),c0)), nf(s0,in(c(hs0),c1)), forall(s0,eq(c0,c1)))
  a4igen.diff.aaa.2(hs0, iff(nf(s0,in(c(hs0),c0)),nf(s0,in(c(hs0),c1))), forall(s0,eq(c0,c1)))
  nf.iffnfid(s0, in(c(hs0),c0), in(c(hs0),c1), forall(s0,eq(c0,c1)))
  a4igen.aaa(s0, eq(c0,c1), iff(in(c(hs0),c0),in(c(hs0),c1)))
  a9.class(c0, c1, c(hs0))
}
```

```follow
thm nfc.iffnfci.1(set s0, class c0, class c1) {
  |- iff(nfc(s0,c0),nfc(s0,c1))
  |- iff(nfc(s0,c1), nfc(s0,c0))
  |- imp(nfc(s0,c0),nfc(s0,c1))
  |- imp(nfc(s0,c1), nfc(s0,c0))
  -| forall(s0, eq(c0,c1)) 
} = {
  iff.comi(nfc(s0,c1), nfc(s0,c0))
  iff.lefti(nfc(s0,c0), nfc(s0,c1))
  iff.righti(nfc(s0,c1), nfc(s0,c0))
  mp(iff(nfc(s0,c0),nfc(s0,c1)), forall(s0,eq(c0,c1)))
  nfc.iffnfc.1(s0, c0, c1)
}
```

```follow
thm nfc.iffnfcid.1(set s0, class c0, class c1, prop p0) {
  |- imp(p0, iff(nfc(s0,c0),nfc(s0,c1)))
  |- imp(p0, iff(nfc(s0,c1), nfc(s0,c0)))
  |- imp(p0, imp(nfc(s0,c0),nfc(s0,c1)))
  |- imp(p0, imp(nfc(s0,c1), nfc(s0,c0)))
  -| imp(p0, forall(s0, eq(c0,c1)))
} = {
  iff.comid(p0, nfc(s0,c1), nfc(s0,c0))
  iff.leftid(p0, nfc(s0,c0), nfc(s0,c1))
  iff.rightid(p0, nfc(s0,c1), nfc(s0,c0))
  syl(p0, iff(nfc(s0,c0),nfc(s0,c1)), forall(s0,eq(c0,c1)))
  nfc.iffnfc.1(s0, c0, c1)
}
```

```follow
thm nfc.iffnfcigen.1(set s0, class c0, class c1) {
  |- iff(nfc(s0,c0),nfc(s0,c1))
  |- iff(nfc(s0,c1),nfc(s0,c0))
  |- imp(nfc(s0,c0),nfc(s0,c1))
  |- imp(nfc(s0,c1),nfc(s0,c0))
  -| eq(c0,c1)
} = {
  iff.comi(nfc(s0,c1), nfc(s0,c0))
  iff.lefti(nfc(s0,c0), nfc(s0,c1))
  iff.righti(nfc(s0,c1), nfc(s0,c0))
  nfc.iffnfci.1(s0, c0, c1)
  gen.forall(s0, eq(c0,c1))
}
```

```follow
thm nfc.iffnfcidgen.1(set s0, class c0, class c1, prop p0) {
  |- imp(p0, iff(nfc(s0,c0),nfc(s0,c1)))
  |- imp(p0, iff(nfc(s0,c1),nfc(s0,c0)))
  |- imp(p0, imp(nfc(s0,c0),nfc(s0,c1)))
  |- imp(p0, imp(nfc(s0,c1),nfc(s0,c0)))
  -| imp(p0, eq(c0,c1))
  -| nf(s0, p0)
} = {
  iff.comid(p0, nfc(s0,c1), nfc(s0,c0))
  iff.leftid(p0, nfc(s0,c0), nfc(s0,c1))
  iff.rightid(p0, nfc(s0,c1), nfc(s0,c0))
  nfc.iffnfcid.1(s0, c0, c1, p0)
  nf.a4igen.aea.1(s0, p0, eq(c0,c1))
}
```

```follow
thm nfc.iffnfciigen.1(set s0, class c0, class c1) {
  |- nfc(s0,c0)
  -| nfc(s0, c1)
  -| eq(c1,c0)
} = {
  mp(nfc(s0,c0), nfc(s0,c1))
  nfc.iffnfcigen.1(s0, c1, c0)
}
```

```follow
thm nfc.rw3(set s0, class c0, class c1, prop p0) {
  |- imp(p0, nfc(s0,c0))
  -| imp(p0, nfc(s0,c1))
  -| eq(c0,c1)
} = {
  mpd(p0, nfc(s0,c0), nfc(s0,c1))
  nfc.iffnfcid.1(s0, c0, c1, p0)
  a1i(p0, forall(s0,eq(c0,c1)))
  gen.forall(s0, eq(c0,c1))
}
```

```follow
thm nfc.diff(set s0, class c0) {
  |- nfc(s0, c0)
  diff (s0, c0)
} = {
  nfc.defigen.2(s0, c0, hs0)
  nf.diff(s0, in(c(hs0),c0))
}
```

```follow
thm nfc.cab.id(set s0, prop p0) {
  |- nfc(s0, cab(s0,p0))
} = {
  nfc.defigen.2(s0, cab(s0,p0), hs0)
  cab.nf.1(p0, s0, hs0)
}
```

```follow
thm nf.nfc.1(set s0, class c0) {
  |- nf(s0, nfc(s0,c0))
} = {
  mp(nf(s0,nfc(s0,c0)), nf(s0,forall(hs0,nf(s0,in(c(hs0),c0)))))
  nf.iffnfigen(s0, nfc(s0,c0), forall(hs0,nf(s0,in(c(hs0),c0))))
  nfc.def(s0, c0, hs0)
  nf.forall.2(nf(s0,in(c(hs0),c0)), s0, hs0)
  nf.nf.1(s0, in(c(hs0),c0))
}
```

```follow
thm nfc.2nfini(set s0, set s1, class c1) {
  |- nf(s0, in(c(s1),c1))
  -| nfc(s0, c1)
  diff (s0, s1)
} = {
  mp(nf(s0,in(c(s1),c1)), nfc(s0,c1))
  syl(nfc(s0,c1), nf(s0,in(c(s1),c1)), forall(hs0,nf(s0,in(c(hs0),c1))))
  nfc.def.ext(s0, c1, hs0)
  nf.special.1(hs0, s1, nf(s0,in(c(hs0),c1)), nf(s0,in(c(s1),c1)))
  nf.iffnfid(s0, in(c(hs0),c1), in(c(s1),c1), eq(c(hs0),c(s1)))
  nf.diff(hs0, nf(s0,in(c(s1),c1)))
  a4igen.diff.aaa.2(s0, iff(in(c(hs0),c1),in(c(s1),c1)), eq(c(hs0),c(s1)))
  a8.class(c(hs0), c(s1), c1)
}
```

```follow
thm nfc.2insubsi(class c0, set s0, set s1) {
  |- iff(subs(in(c(s0),c0),s0,s1), in(c(s1),c0))
  -| nfc(s0,c0)
} = {
  iff.syl(subs(in(c(s0),c0),s0,s1), in(c(s1),c0), subs(subs(in(c(hs0),c0),hs0,s0),s0,s1))
  subs.iffsubsigen(in(c(s0),c0), subs(in(c(hs0),c0),hs0,s0), s0, s1)
  in.subs.class(c0, hs0, s0)
  iff.syl(subs(subs(in(c(hs0),c0),hs0,s0),s0,s1), in(c(s1),c0), subs(in(c(hs0),c0),hs0,s1))
  nf.subs.trans(hs0, s1, s0, in(c(hs0),c0))
  nfc.2nfini(s0, hs0, c0)
  in.subs.class(c0, hs0, s1)
}
```

```follow
thm nf.2nfccabigen(prop p0, set s0, set s1) {
  |- nfc(s1, cab(s0,p0))
  -| nf(s1, p0)
} = {
  nfc.defigen.2(s1, cab(s0,p0), hs0)
  cab.nf.2(p0, s0, hs0, s1)
}
```

```follow
thm nfc.nfeqiid(set s0, class c0, class c1, prop p0) {
  |- imp(p0, nf(s0, eq(c0,c1)))
  -| imp(p0, nfc(s0, c0))
  -| imp(p0, nfc(s0, c1))
} = {
  syl(p0, nf(s0,eq(c0,c1)), nf(s0,forall(hs0,iff(in(c(hs0),c0),in(c(hs0),c1)))))
  nf.iffnfigen(s0, eq(c0,c1), forall(hs0,iff(in(c(hs0),c0),in(c(hs0),c1))))
  eq.def(c0, c1, hs0)
  nf.forall.3(p0, iff(in(c(hs0),c0),in(c(hs0),c1)), s0, hs0)
  nf.diff(hs0, p0)
  nf.iffiid(s0, in(c(hs0),c0), in(c(hs0),c1), p0)
  nfc.defspid.1(s0, c0, hs0, p0)
  nfc.defspid.1(s0, c1, hs0, p0)
}
```

```follow
thm nfc.nfiniid(set s0, class c0, class c1, prop p0) {
  |- imp(p0, nf(s0,in(c0,c1)))
  -| imp(p0, nfc(s0,c0))
  -| imp(p0, nfc(s0,c1))
} = {
  syl(p0, nf(s0,in(c0,c1)), nf(s0,exist(hs0,and(eq(c(hs0),c0),in(c(hs0),c1)))))
  nf.iffnfigen(s0, exist(hs0,and(eq(c(hs0),c0),in(c(hs0),c1))), in(c0,c1))
  in.def.ext(c0, c1, hs0)
  nf.exist.3(p0, and(eq(c(hs0),c0),in(c(hs0),c1)), s0, hs0)
  nf.diff(hs0, p0)
  nf.andiid(s0, eq(c(hs0),c0), in(c(hs0),c1), p0)
  nfc.nfeqiid(s0, c(hs0), c0, p0)
  a1i(p0, nfc(s0,c(hs0)))
  nfc.diff(s0, c(hs0))
  nfc.defspid.1(s0, c1, hs0, p0)
}
```

```follow
thm nf.nfc.2(set s1, set s0, class c0) {
  |- nf(s1, nfc(s0,c0))
  -| nfc(s1, c0)
} = {
  mp(nf(s1,nfc(s0,c0)), nf(s1,forall(hs0,nf(s0,in(c(hs0),c0)))))
  nf.iffnfigen(s1, nfc(s0,c0), forall(hs0,nf(s0,in(c(hs0),c0))))
  nfc.def(s0, c0, hs0)
  nf.forall.2(nf(s0,in(c(hs0),c0)), s1, hs0)
  nf.nf.2(in(c(hs0),c0), s1, s0)
  nfc.defspi.1(s1, c0, hs0)
}
```

```follow
thm nfc.nfeqii(set s0, class c0, class c1) {
  |- nf(s0, eq(c0,c1))
  -| nfc(s0, c0)
  -| nfc(s0, c1)
} = {
  mp(nf(s0,eq(c0,c1)), nf(s0,forall(hs0,iff(in(c(hs0),c0),in(c(hs0),c1)))))
  nf.iffnfigen(s0, forall(hs0,iff(in(c(hs0),c0),in(c(hs0),c1))), eq(c0,c1))
  eq.def.ext(c0, c1, hs0)
  nf.forall.2(iff(in(c(hs0),c0),in(c(hs0),c1)), s0, hs0)
  nf.iffii(s0, in(c(hs0),c0), in(c(hs0),c1))
  nfc.2nfini(s0, hs0, c0)
  nfc.2nfini(s0, hs0, c1)
}
```

```follow
thm nfc.nfinii(set s0, class c0, class c1) {
  |- nf(s0,in(c0,c1))
  -| nfc(s0,c0)
  -| nfc(s0,c1)
} = {
  mp(nf(s0,in(c0,c1)), nf(s0,exist(hs0,and(eq(c(hs0),c0),in(c(hs0),c1)))))
  nf.iffnfigen(s0, exist(hs0,and(eq(c(hs0),c0),in(c(hs0),c1))), in(c0,c1))
  in.def.ext(c0, c1, hs0)
  nf.exist.2(and(eq(c(hs0),c0),in(c(hs0),c1)), s0, hs0)
  nf.andii(s0, eq(c(hs0),c0), in(c(hs0),c1))
  nfc.nfeqii(s0, c(hs0), c0)
  nfc.2nfini(s0, hs0, c1)
  nfc.diff(s0, c(hs0))
}
```

```follow
thm nfc.iffnfc.2(set s0, set s1, class c0, class c1) {
  |- imp(forall(s0, eq(c(s0),c(s1))), iff(nfc(s0,c0),nfc(s1,c1)))
  |- imp(forall(s0, eq(c(s0),c(s1))), iff(nfc(s1,c1), nfc(s0,c0)))
  |- imp(forall(s0, eq(c(s0),c(s1))), imp(nfc(s0,c0),nfc(s1,c1)))
  |- imp(forall(s0, eq(c(s0),c(s1))), imp(nfc(s1,c1), nfc(s0,c0)))
  -| imp(forall(s0, eq(c(s0),c(s1))), eq(c0,c1))
} = {
  iff.comid(forall(s0,eq(c(s0),c(s1))), nfc(s1,c1), nfc(s0,c0))
  iff.leftid(forall(s0,eq(c(s0),c(s1))), nfc(s0,c0), nfc(s1,c1))
  iff.rightid(forall(s0,eq(c(s0),c(s1))), nfc(s1,c1), nfc(s0,c0))
  iff.rw23(forall(s0,eq(c(s0),c(s1))), nfc(s0,c0), nfc(s1,c1), forall(hs0,nf(s0,in(c(hs0),c0))), forall(hs0,nf(s1,in(c(hs0),c1))))
  nfc.def(s0, c0, hs0)
  nfc.def(s1, c1, hs0)
  a4id.aaa.iff(hs0, nf(s0,in(c(hs0),c0)), nf(s1,in(c(hs0),c1)), forall(s0,eq(c(s0),c(s1))))
  a4igen.diff.aaa.2(hs0, iff(nf(s0,in(c(hs0),c0)),nf(s1,in(c(hs0),c1))), forall(s0,eq(c(s0),c(s1))))
  foralleq.nf.rw(s0, s1, in(c(hs0),c0), in(c(hs0),c1))
  in.iffiniid(c(hs0), c0, c(hs0), c1, forall(s0,eq(c(s0),c(s1))))
  eq.idd.class(c(hs0), forall(s0,eq(c(s0),c(s1))))
}
```

```follow
thm nfc.iffnfc.3(set s0, set s1, set s2, class c0, class c1) {
  |- imp(forall(s0, eq(c(s0),c(s1))), iff(nfc(s2,c0),nfc(s2,c1)))
  -| imp(forall(s0, eq(c(s0),c(s1))), eq(c0,c1))
} = {
  nfc.iffnfcid.1(s2, c0, c1, forall(s0,eq(c(s0),c(s1))))
  nf.a4igen.aea.1(s2, forall(s0,eq(c(s0),c(s1))), eq(c0,c1))
  nf.forall.eq.1(s2, s0, s1)
}
```

```follow
thm nfc.cabd(set s0, set s1, prop p0, prop p1) {
  |- imp(p0, nfc(s0, cab(s1, p1)))
  -| imp(p0, nf(s0, p1))
  -| nf(s1, p0)
} = {
  nfc.defspid.2(s0, cab(s1,p1), hs0, p0)
  syl(p0, nf(s0,in(c(hs0),cab(s1,p1))), nf(s0,subs(p1,s1,hs0)))
  nf.iffnfigen(s0, in(c(hs0),cab(s1,p1)), subs(p1,s1,hs0))
  cab.def.1(hs0, s1, p1)
  nf.subs.3(s0, s1, hs0, p0, p1)
}
```

```follow
thm nfc.cabd.and(set s0, set s1, prop p0, prop p1) {
  |- imp(p0, nfc(s0, cab(s1, p1)))
  -| imp(and(p0,not(forall(s0,eq(c(s0),c(s1))))), nf(s0, p1))
  -| nf(s1, p0)
} = {
  contii.4(imp(p0,nfc(s0,cab(s1,p1))), forall(s0,eq(c(s0),c(s1))))
  com12i(not(forall(s0,eq(c(s0),c(s1)))), p0, nfc(s0,cab(s1,p1)))
  and.spliti(p0, not(forall(s0,eq(c(s0),c(s1)))), nfc(s0,cab(s1,p1)))
  nfc.cabd(s0, s1, and(p0,not(forall(s0,eq(c(s0),c(s1))))), p1)
  nf.andii(s1, p0, not(forall(s0,eq(c(s0),c(s1)))))
  nf.noti(s1, forall(s0,eq(c(s0),c(s1))))
  nf.forall.eq.1(s1, s0, s1)
  a1id(forall(s0,eq(c(s0),c(s1))), p0, nfc(s0,cab(s1,p1)))
  mpi(forall(s0,eq(c(s0),c(s1))), nfc(s0,cab(s1,p1)), nfc(s1,cab(s1,p1)))
  nfc.cab.id(s1, p1)
  syl(forall(s0,eq(c(s0),c(s1))), imp(nfc(s1,cab(s1,p1)),nfc(s0,cab(s1,p1))), forall(s1,eq(c(s1),c(s0))))
  nfc.iffnfc.2(s1, s0, cab(s1,p1), cab(s1,p1))
  eq.rw(s0, s1)
  eq.idd.class(cab(s1,p1), forall(s1,eq(c(s1),c(s0))))
}
```

```follow
thm nfc.neq.1(set s0, set s1, set s2, class c0, class c1, prop p0) {
  |- imp(p0, imp(not(forall(s0,eq(c(s0),c(s1)))), nfc(s0,c0)))
  -| imp(p0, imp(eq(c(s2),c(s1)), eq(c1,c0)))
  -| imp(p0, nfc(s0,c1))
  -| imp(p0, nfc(s2,c0))
  -| nf(s0, p0)
  -| nf(s2, p0)
} = {
  and.spliti(p0, not(forall(s0,eq(c(s0),c(s1)))), nfc(s0,c0))
  nfc.defid.2(s0, c0, hs0, and(p0,not(forall(s0,eq(c(s0),c(s1))))))
  a4igen.diff.aaa.2(hs0, nf(s0,in(c(hs0),c0)), and(p0,not(forall(s0,eq(c(s0),c(s1))))))
  and.joini(p0, not(forall(s0,eq(c(s0),c(s1)))), nf(s0,in(c(hs0),c0)))
  nf.neq.6(s0, s1, s2, p0, in(c(hs0),c0), in(c(hs0),c1))
  rw3(p0, eq(c(s2),c(s1)), iff(in(c(hs0),c1),in(c(hs0),c0)), eq(c1,c0))
  a9.class(c1, c0, c(hs0))
  nfc.nfiniid(s0, c(hs0), c1, p0)
  nfc.nfiniid(s2, c(hs0), c0, p0)
  a1i(p0, nfc(s2,c(hs0)))
  nfc.diff(s2, c(hs0))
  a1i(p0, nfc(s0,c(hs0)))
  nfc.diff(s0, c(hs0))
}
```

```follow
thm nfc.neq.2(set s0, set s1, set s2, class c0, class c1) {
  |- imp(not(forall(s0,eq(c(s0),c(s1)))), nfc(s0,c0))
  -| imp(eq(c(s2),c(s1)), eq(c1, c0))
  -| nfc(s0, c1)
  -| nfc(s2, c0)
} = {
  mp(imp(not(forall(s0,eq(c(s0),c(s1)))),nfc(s0,c0)), eq(c(hs0),c(hs0)))
  eq.id(hs0)
  nfc.neq.1(s0, s1, s2, c0, c1, eq(c(hs0),c(hs0)))
  a1i(eq(c(hs0),c(hs0)), imp(eq(c(s2),c(s1)),eq(c1,c0)))
  a1i(eq(c(hs0),c(hs0)), nfc(s0,c1))
  a1i(eq(c(hs0),c(hs0)), nfc(s2,c0))
  nf.diff(s0, eq(c(hs0),c(hs0)))
  nf.diff(s2, eq(c(hs0),c(hs0)))
}
```

```follow
thm nfc.neq.set(set s0, set s1) {
  |- imp(not(forall(s0,eq(c(s0),c(s1)))), nfc(s0,c(s1)))
} = {
  syl(not(forall(s0,eq(c(s0),c(s1)))), nfc(s0,c(s1)), forall(hs0,nf(s0,in(c(hs0),c(s1)))))
  nfc.def.ext(s0, c(s1), hs0)
  a4igen.diff.aaa.2(hs0, nf(s0,in(c(hs0),c(s1))), not(forall(s0,eq(c(s0),c(s1)))))
  nf.neq.5(in(c(hs0),c(s1)), in(c(hs0),c(hs1)), s0, s1, hs1)
  a9.class(c(hs1), c(s1), c(hs0))
  nf.diff(s0, in(c(hs0),c(hs1)))
  nf.diff(hs1, in(c(hs0),c(s1)))
}
```

```follow
thm nfc.neq.set.2(set s0, set s1) {
  |- imp(not(forall(s0,eq(c(s1),c(s0)))), nfc(s0,c(s1)))
} = {
  syl(not(forall(s0,eq(c(s1),c(s0)))), nfc(s0,c(s1)), not(forall(s0,eq(c(s0),c(s1)))))
  nfc.neq.set(s0, s1)
  coni.4(forall(s0,eq(c(s1),c(s0))), forall(s0,eq(c(s0),c(s1))))
  forall.eq.com(s0, s0, s1)
}
```

```follow
thm eq.class.nfc(set s0, class c0, class c1) {
  |- iff(eq(c0, c1), forall(s0, iff(in(c(s0),c0), in(c(s0),c1))))
  -| nfc(s0, c0)
  -| nfc(s0, c1)
} = {
  iff.introii.1(eq(c0,c1), forall(s0,iff(in(c(s0),c0),in(c(s0),c1))))
  eq.defigend(c0, c1, hs0, forall(s0,iff(in(c(s0),c0),in(c(s0),c1))))
  forall.special.1(s0, hs0, iff(in(c(s0),c0),in(c(s0),c1)), iff(in(c(hs0),c0),in(c(hs0),c1)))
  iff.2iffiid.2(in(c(s0),c0), in(c(s0),c1), in(c(hs0),c0), in(c(hs0),c1), eq(c(s0),c(hs0)))
  a8.class(c(s0), c(hs0), c0)
  a8.class(c(s0), c(hs0), c1)
  nf.a5(not(iff(in(c(hs0),c0),in(c(hs0),c1))), s0)
  nf.noti(s0, iff(in(c(hs0),c0),in(c(hs0),c1)))
  nf.iffii(s0, in(c(hs0),c0), in(c(hs0),c1))
  nfc.2nfini(s0, hs0, c0)
  nfc.nfinii(s0, c(hs0), c1)
  nfc.diff(s0, c(hs0))

  nf.a4igen.aea.1(s0, eq(c0,c1), iff(in(c(s0),c0),in(c(s0),c1)))
  a9.class(c0, c1, c(s0))
  nfc.nfeqii(s0, c0, c1)
}
```

```follow
thm nfc.cab.eq.1(set s0, class c0) {
  |- eq(cab(s0, in(c(s0),c0)), c0)
  -| nfc(s0, c0)
} = {
  mp(eq(cab(s0,in(c(s0),c0)),c0), forall(hs0,iff(in(c(hs0),cab(s0,in(c(s0),c0))),in(c(hs0),c0))))
  eq.def.ext(cab(s0,in(c(s0),c0)), c0, hs0)
  gen.forall(hs0, iff(in(c(hs0),cab(s0,in(c(s0),c0))),in(c(hs0),c0)))
  iff.syl(in(c(hs0),cab(s0,in(c(s0),c0))), in(c(hs0),c0), subs(in(c(s0),c0),s0,hs0))
  cab.def.1(hs0, s0, in(c(s0),c0))
  nfc.2insubsi(c0, s0, hs0)
}
```

```follow
thm nfc.cab.eq.2(set s0, class c0, prop p0) {
  |- iff(eq(c0,cab(s0,p0)), forall(s0, iff(in(c(s0),c0), p0)))
  -| nfc(s0, c0)
} = {
  iff.syl(eq(c0,cab(s0,p0)), forall(s0,iff(in(c(s0),c0),p0)), forall(s0,iff(in(c(s0),c0),in(c(s0),cab(s0,p0)))))
  eq.class.nfc(s0, c0, cab(s0,p0))
  nfc.cab.id(s0, p0)
  a4igen.aaa.iff(s0, iff(in(c(s0),c0),in(c(s0),cab(s0,p0))), iff(in(c(s0),c0),p0))
  iff.transi.2(p0, in(c(s0),cab(s0,p0)), in(c(s0),c0))
  cab.id(p0, s0)
}
```
