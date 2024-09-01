
# `Extension` 

```follow
axiom axext.1(set s0, set s1, set s2) {
  |- imp(forall(s2, iff(in(c(s2), c(s0)), in(c(s2), c(s1)))), eq(c(s0), c(s1)))
  diff (s0, s1, s2)
}
```

```follow
thm axext.2(set s0, set s1, set s2) {
  |- imp(forall(s2, iff(in(c(s2), c(s0)), in(c(s2), c(s1)))), forall(s2, eq(c(s0), c(s1))))
  diff (s0, s1, s2)
} = {
  syl(forall(s2,iff(in(c(s2),c(s0)),in(c(s2),c(s1)))), forall(s2,eq(c(s0),c(s1))), eq(c(s0),c(s1)))
  axext.1(s0, s1, s2)
  a5.forall.1(s2, eq(c(s0),c(s1)))
}
```

```follow
thm axext.3(set s0, set s1, set s2) {
  |- exist(s2, imp(iff(in(c(s2), c(s0)), in(c(s2), c(s1))), eq(c(s0), c(s1))))
  diff (s0, s1, s2)
} = {
  mp(exist(s2,imp(iff(in(c(s2),c(s0)),in(c(s2),c(s1))),eq(c(s0),c(s1)))), imp(forall(s2,iff(in(c(s2),c(s0)),in(c(s2),c(s1)))),eq(c(s0),c(s1))))
  axext.1(s0, s1, s2)
  a4.diff.eae.2(s2, iff(in(c(s2),c(s0)),in(c(s2),c(s1))), eq(c(s0),c(s1)))
}
```

```follow
thm axext.4(set s0, set s1, set s2) {
  |- imp(forall(s2, iff(in(c(s2), c(s0)), in(c(s2), c(s1)))), eq(c(s0), c(s1)))
  diff (s0, s2) (s1, s2)
} = {
  exist.mp(hs0, imp(forall(s2,iff(in(c(s2),c(s0)),in(c(s2),c(s1)))),eq(c(s0),c(s1))), eq(c(hs0),c(s0)))
  a6.exist(hs0, s0)
  syld(eq(c(hs0),c(s0)), forall(s2,iff(in(c(s2),c(s0)),in(c(s2),c(s1)))), eq(c(s0),c(s1)), eq(c(hs0),c(s1)))
  eq.trans.1(hs0, s0, s1)
  rw3(eq(c(hs0),c(s0)), forall(s2,iff(in(c(s2),c(s0)),in(c(s2),c(s1)))), eq(c(hs0),c(s1)), forall(s2,iff(in(c(s2),c(hs0)),in(c(s2),c(s1)))))
  a4id.aaa(s2, iff(in(c(s2),c(s0)),in(c(s2),c(s1))), iff(in(c(s2),c(hs0)),in(c(s2),c(s1))), eq(c(hs0),c(s0)))
  gend(s2, imp(iff(in(c(s2),c(s0)),in(c(s2),c(s1))),iff(in(c(s2),c(hs0)),in(c(s2),c(s1)))), eq(c(hs0),c(s0)))
  syl(eq(c(hs0),c(s0)), imp(iff(in(c(s2),c(s0)),in(c(s2),c(s1))),iff(in(c(s2),c(hs0)),in(c(s2),c(s1)))), iff(in(c(s2),c(s0)),in(c(s2),c(hs0))))
  iff.trans.2(in(c(s2),c(s1)), in(c(s2),c(s0)), in(c(s2),c(hs0)))
  a9(hs0, s0, s2)
  axext.1(hs0, s1, s2)
}
```

```follow
thm axext.5(set s0, set s1, set s2) {
  |- imp(forall(s2, iff(in(c(s2), c(s0)), in(c(s2), c(s1)))), eq(c(s0), c(s1)))
  |- imp(eq(c(s0), c(s1)), forall(s2, iff(in(c(s2), c(s0)), in(c(s2), c(s1)))))
  |- iff(forall(s2, iff(in(c(s2), c(s0)), in(c(s2), c(s1)))), eq(c(s0), c(s1)))
  |- iff(eq(c(s0), c(s1)), forall(s2, iff(in(c(s2), c(s0)), in(c(s2), c(s1)))))
  diff (s0, s2) (s1, s2)
} = {
  iff.introii.1(forall(s2,iff(in(c(s2),c(s0)),in(c(s2),c(s1)))), eq(c(s0),c(s1)))
  iff.introii.1(eq(c(s0),c(s1)), forall(s2,iff(in(c(s2),c(s0)),in(c(s2),c(s1)))))
  axext.4(s0, s1, s2)
  a4igen.diff.aaa.2(s2, iff(in(c(s2),c(s0)),in(c(s2),c(s1))), eq(c(s0),c(s1)))
  a9(s0, s1, s2)
}
```




