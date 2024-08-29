
# 非自由变量 `notfree` 

非自由变量的概念在一阶逻辑里非常重要，它指的是 $\forall x, p$ 或者 $\exists x, p$ 之类命题与变量 $x$ 的关系。在这些句子中，$x$ 不是自由的(not free)，无论 $x$ 取到什么值，都对整个句子的真假性没有影响。

在通常的数理逻辑教材中，会从语法(Syntax)层面定义什么叫做**自由变量**，什么叫做**非自由变量**。比如,自由变量的语法上的定义是：
- 出现在命题 $p$ 中，但是没有在 $(\forall x, ...)$ 和 $(\exist x, ...)$ 中的 $x$ 叫做 $p$ 的自由变量。

对应的， **非自由变量** 的语法上的定义是：
- $x$ 没有在命题 $p$ 中出现过，那么 $x$ 是 $p$ 的非自由变量；
- 或者 $x$ 在 $p$ 中出现过，但是都是出现在 $\forall$ 符号，或者 $\exists$ 符号旁边，那么 $x$ 是 $p$ 的非自由变量。

这里有两种情况。第一种情况非常容易判断，只需要检查一下命题p中有没有出现x。在 `Follow` 语言中把这种情况单独拿了出来，设计成一个语法规则，`diff`，让编译器自动帮我们判断是否正确。

因为 $\forall$ 和 $\exists$ 没有绑定到 `Follow` 的语法中，我们没有办法在在语法层面定义`notfree`的第二种情况。所以，我们需要在逻辑层面构建 `notfree` 这一概念。

```follow
term prop nf(set s0, prop p0) { ㎋(s0, p0) }
```

```follow
axiom nf.def.1(set s0, prop p0) {
  |- iff(nf(s0, p0), imp(exist(s0,p0), forall(s0,p0)))
}
```

```follow
thm nf.def.1.ext(set s0, prop p0) {
  |- iff(imp(exist(s0,p0), forall(s0,p0)), nf(s0, p0))
  |- imp(nf(s0, p0), imp(exist(s0,p0), forall(s0,p0)))
  |- imp(imp(exist(s0,p0), forall(s0,p0)), nf(s0, p0))
} = {
  iff.comi(imp(exist(s0,p0),forall(s0,p0)), nf(s0,p0))
  iff.lefti(nf(s0,p0), imp(exist(s0,p0),forall(s0,p0)))
  iff.righti(imp(exist(s0,p0),forall(s0,p0)), nf(s0,p0))
  nf.def.1(s0, p0)
}
```

## 等价定义

```follow
thm nf.def.2(set s0, prop p0) {
  |- iff(nf(s0, p0), or(forall(s0,p0), not(exist(s0, p0))))
  |- iff(or(forall(s0,p0), not(exist(s0, p0))), nf(s0, p0))
  |- imp(nf(s0, p0), or(forall(s0,p0), not(exist(s0, p0))))
  |- imp(or(forall(s0,p0), not(exist(s0, p0))), nf(s0, p0))
} = {
  iff.comi(or(forall(s0,p0),not(exist(s0,p0))), nf(s0,p0))
  iff.lefti(nf(s0,p0), or(forall(s0,p0),not(exist(s0,p0))))
  iff.righti(or(forall(s0,p0),not(exist(s0,p0))), nf(s0,p0))
  iff.syl(nf(s0,p0), or(forall(s0,p0),not(exist(s0,p0))), imp(exist(s0,p0),forall(s0,p0)))
  nf.def.1(s0, p0)
  iff.syl(imp(exist(s0,p0),forall(s0,p0)), or(forall(s0,p0),not(exist(s0,p0))), imp(not(forall(s0,p0)),not(exist(s0,p0))))
  iff.or.def(forall(s0,p0), not(exist(s0,p0)))
  iff.con(exist(s0,p0), forall(s0,p0))
}
```

```follow
thm nf.def.3(set s0, prop p0) {
  |- iff(nf(s0, p0), or(forall(s0,p0), forall(s0, not(p0))))
  |- iff(or(forall(s0,p0), forall(s0, not(p0))), nf(s0, p0))
  |- imp(nf(s0, p0), or(forall(s0,p0), forall(s0, not(p0))))
  |- imp(or(forall(s0,p0), forall(s0, not(p0))), nf(s0, p0))
} = {
  iff.comi(or(forall(s0,p0),forall(s0,not(p0))), nf(s0,p0))
  iff.lefti(nf(s0,p0), or(forall(s0,p0),forall(s0,not(p0))))
  iff.righti(or(forall(s0,p0),forall(s0,not(p0))), nf(s0,p0))
  iff.syl(nf(s0,p0), or(forall(s0,p0),forall(s0,not(p0))), or(forall(s0,p0),not(exist(s0,p0))))
  nf.def.2(s0, p0)
  or.ifforii(forall(s0,p0), forall(s0,p0), not(exist(s0,p0)), forall(s0,not(p0)))
  iff.id(forall(s0,p0))
  exist.def.3(s0, p0)
}
```

```follow
thm nf.def.4(set s0, prop p0) {
  |- iff(nf(s0, p0), imp(not(forall(s0,p0)), forall(s0, not(p0))))
  |- iff(imp(not(forall(s0,p0)), forall(s0, not(p0))), nf(s0, p0))
  |- imp(nf(s0, p0), imp(not(forall(s0,p0)), forall(s0, not(p0))))
  |- imp(imp(not(forall(s0,p0)), forall(s0, not(p0))), nf(s0, p0))
} = {
  iff.comi(imp(not(forall(s0,p0)),forall(s0,not(p0))), nf(s0,p0))
  iff.lefti(nf(s0,p0), imp(not(forall(s0,p0)),forall(s0,not(p0))))
  iff.righti(imp(not(forall(s0,p0)),forall(s0,not(p0))), nf(s0,p0))
  iff.syl(nf(s0,p0), imp(not(forall(s0,p0)),forall(s0,not(p0))), or(forall(s0,p0),forall(s0,not(p0))))
  nf.def.3(s0, p0)
  iff.or.def(forall(s0,p0), forall(s0,not(p0)))
}
```

```follow
thm nf.intro.1(set s0, prop p0) {
  |- imp(forall(s0, p0), nf(s0, p0))
  |- imp(not(exist(s0, p0)), nf(s0, p0))
  |- imp(forall(s0, not(p0)), nf(s0, p0))
} = {
  syl(forall(s0,p0), nf(s0,p0), imp(exist(s0,p0),forall(s0,p0)))
  nf.def.1.ext(s0, p0)
  a1(forall(s0,p0), exist(s0,p0))
  syl(not(exist(s0,p0)), nf(s0,p0), imp(exist(s0,p0),forall(s0,p0)))
  nf.def.1.ext(s0, p0)
  cont.1(exist(s0,p0), forall(s0,p0))
  syl(forall(s0,not(p0)), nf(s0,p0), imp(exist(s0,p0),forall(s0,p0)))
  nf.def.1.ext(s0, p0)
  syl(forall(s0,not(p0)), imp(exist(s0,p0),forall(s0,p0)), not(exist(s0,p0)))
  cont.1(exist(s0,p0), forall(s0,p0))
  exist.def.3(s0, p0)
}
```

## `a4`

```follow
thm nf.a4.origin.aea(set s0, prop p0, prop p1) {
  |- imp(nf(s0,p0), iff(imp(exist(s0,p0), forall(s0,p1)), forall(s0, imp(p0,p1))))
  |- imp(nf(s0,p0), iff(forall(s0, imp(p0,p1)), imp(exist(s0,p0), forall(s0,p1))))
  |- imp(nf(s0,p0), imp(imp(exist(s0,p0), forall(s0,p1)), forall(s0, imp(p0,p1))))
  |- imp(nf(s0,p0), imp(forall(s0, imp(p0,p1)), imp(exist(s0,p0), forall(s0,p1))))
} = {
  iff.introiid.1(nf(s0,p0), imp(exist(s0,p0),forall(s0,p1)), forall(s0,imp(p0,p1)))
  iff.introiid.1(nf(s0,p0), forall(s0,imp(p0,p1)), imp(exist(s0,p0),forall(s0,p1)))
  a1i(nf(s0,p0), imp(imp(exist(s0,p0),forall(s0,p1)),forall(s0,imp(p0,p1))))
  syl(nf(s0,p0), imp(forall(s0,imp(p0,p1)),imp(exist(s0,p0),forall(s0,p1))), imp(exist(s0,p0),forall(s0,p0)))
  nf.def.1.ext(s0, p0)
  com12i(imp(exist(s0,p0),forall(s0,p0)), forall(s0,imp(p0,p1)), imp(exist(s0,p0),forall(s0,p1)))
  syl(forall(s0,imp(p0,p1)), imp(imp(exist(s0,p0),forall(s0,p0)),imp(exist(s0,p0),forall(s0,p1))), imp(forall(s0,p0),forall(s0,p1)))
  trans.1(exist(s0,p0), forall(s0,p0), forall(s0,p1))
  a4.aaa(s0, p0, p1)
  a4.aea(s0, p0, p1)
}
```

```follow
thm nf.a4.origin.aea.iff(set s0, prop p0, prop p1) {
  |- imp(nf(s0,p1), iff(imp(exist(s0,p0), forall(s0,p1)), forall(s0, imp(p0,p1))))
  |- imp(nf(s0,p1), iff(forall(s0, imp(p0,p1)), imp(exist(s0,p0), forall(s0,p1))))
  |- imp(nf(s0,p1), imp(imp(exist(s0,p0), forall(s0,p1)), forall(s0, imp(p0,p1))))
  |- imp(nf(s0,p1), imp(forall(s0, imp(p0,p1)), imp(exist(s0,p0), forall(s0,p1))))
} = {
  iff.introiid.1(nf(s0,p1), imp(exist(s0,p0),forall(s0,p1)), forall(s0,imp(p0,p1)))
  iff.introiid.1(nf(s0,p1), forall(s0,imp(p0,p1)), imp(exist(s0,p0),forall(s0,p1)))
  a1i(nf(s0,p1), imp(imp(exist(s0,p0),forall(s0,p1)),forall(s0,imp(p0,p1))))
  syl(nf(s0,p1), imp(forall(s0,imp(p0,p1)),imp(exist(s0,p0),forall(s0,p1))), imp(exist(s0,p1),forall(s0,p1)))
  nf.def.1.ext(s0, p1)
  com12i(imp(exist(s0,p1),forall(s0,p1)), forall(s0,imp(p0,p1)), imp(exist(s0,p0),forall(s0,p1)))
  syl(forall(s0,imp(p0,p1)), imp(imp(exist(s0,p1),forall(s0,p1)),imp(exist(s0,p0),forall(s0,p1))), imp(exist(s0,p0),exist(s0,p1)))
  trans.2(exist(s0,p0), exist(s0,p1), forall(s0,p1))
  a4.aee(s0, p0, p1)
  a4.aea(s0, p0, p1)
}
```

```follow
thm nf.a4.aea(set s0, prop p0, prop p1) {
  |- iff(imp(exist(s0,p0), forall(s0,p1)), forall(s0, imp(p0,p1)))
  |- iff(forall(s0, imp(p0,p1)), imp(exist(s0,p0), forall(s0,p1)))
  |- imp(imp(exist(s0,p0), forall(s0,p1)), forall(s0, imp(p0,p1)))
  |- imp(forall(s0, imp(p0,p1)), imp(exist(s0,p0), forall(s0,p1)))
  -| nf(s0, p0)
} = {
  mp(iff(imp(exist(s0,p0),forall(s0,p1)),forall(s0,imp(p0,p1))), nf(s0,p0))
  mp(iff(forall(s0,imp(p0,p1)),imp(exist(s0,p0),forall(s0,p1))), nf(s0,p0))
  mp(imp(imp(exist(s0,p0),forall(s0,p1)),forall(s0,imp(p0,p1))), nf(s0,p0))
  mp(imp(forall(s0,imp(p0,p1)),imp(exist(s0,p0),forall(s0,p1))), nf(s0,p0))
  nf.a4.origin.aea(s0, p0, p1)
}
```

## `diff` 

```follow
thm nf.diff(set s0, prop p0) {
  |- nf(s0, p0)
  diff (s0, p0)
} = {
  mp(nf(s0,p0), imp(exist(s0,p0),forall(s0,p0)))
  nf.def.1.ext(s0, p0)
  a5.exist.forall(s0, p0)
}
```

## `gen`

```follow
thm nf.gen(set s0, prop p0) {
  |- nf(s0, p0)
  -| p0
} = {
  mp(nf(s0,p0), forall(s0,p0))
  nf.intro.1(s0, p0)
  gen.forall(s0, p0)
}
```

## `nf.iffnf`

```follow
thm nf.iffnf(set s0, prop p0, prop p1) {
  |- imp(forall(s0, iff(p0, p1)), iff(nf(s0,p0),nf(s0,p1)))
} = {
  iff.rw23(forall(s0,iff(p0,p1)), nf(s0,p0), nf(s0,p1), imp(exist(s0,p0),forall(s0,p0)), imp(exist(s0,p1),forall(s0,p1)))
  nf.def.1(s0, p0)
  nf.def.1(s0, p1)
  imp.iffimpiid.3(forall(s0,iff(p0,p1)), exist(s0,p0), forall(s0,p0), exist(s0,p1), forall(s0,p1))
  a4.aaa.iff(s0, p0, p1)
  a4.aee.iff(s0, p0, p1)
}
```

```follow
thm nf.iffnfi(set s0, prop p0, prop p1) {
  |- iff(nf(s0,p0),nf(s0,p1))
  |- iff(nf(s0,p1), nf(s0,p0))
  |- imp(nf(s0,p0),nf(s0,p1))
  |- imp(nf(s0,p1), nf(s0,p0))
  -| forall(s0, iff(p0, p1)) 
} = {
  iff.comi(nf(s0,p1), nf(s0,p0))
  iff.lefti(nf(s0,p0), nf(s0,p1))
  iff.righti(nf(s0,p1), nf(s0,p0))
  mp(iff(nf(s0,p0),nf(s0,p1)), forall(s0,iff(p0,p1)))
  nf.iffnf(s0, p0, p1)
}
```

```follow
thm nf.iffnfd(set s0, prop p0, prop p1, prop p2) {
  |- imp(p2, iff(nf(s0,p0),nf(s0,p1)))
  |- imp(p2, iff(nf(s0,p1), nf(s0,p0)))
  |- imp(p2, imp(nf(s0,p0),nf(s0,p1)))
  |- imp(p2, imp(nf(s0,p1), nf(s0,p0)))
  -| imp(p2, forall(s0, iff(p0, p1)))
} = {
  iff.comid(p2, nf(s0,p1), nf(s0,p0))
  iff.leftid(p2, nf(s0,p0), nf(s0,p1))
  iff.rightid(p2, nf(s0,p1), nf(s0,p0))
  syl(p2, iff(nf(s0,p0),nf(s0,p1)), forall(s0,iff(p0,p1)))
  nf.iffnf(s0, p0, p1)
}
```

```follow
thm nf.iffnfigen(set s0, prop p0, prop p1) {
  |- iff(nf(s0,p0),nf(s0,p1))
  |- iff(nf(s0,p1), nf(s0,p0))
  |- imp(nf(s0,p0),nf(s0,p1))
  |- imp(nf(s0,p1), nf(s0,p0))
  -| iff(p0, p1)
} = {
  nf.iffnfi(s0, p0, p1)
  gen.forall(s0, iff(p0,p1))
}
```

```follow
thm nf.rw(set s0, prop p0, prop p1) {
  |- nf(s0, p0)
  -| nf(s0, p1)
  -| iff(p1, p0)
} = {
  mp(nf(s0,p0), nf(s0,p1))
  nf.iffnfigen(s0, p1, p0)
}
```

## `nf` 与 `not` 

```follow
thm nf.not(set s0, prop p0) {
  |- iff(nf(s0,p0),nf(s0,not(p0)))
  |- iff(nf(s0,not(p0)), nf(s0,p0))
  |- imp(nf(s0,p0),nf(s0,not(p0)))
  |- imp(nf(s0,not(p0)), nf(s0,p0))
} = {
  iff.comi(nf(s0,not(p0)), nf(s0,p0))
  iff.lefti(nf(s0,p0), nf(s0,not(p0)))
  iff.righti(nf(s0,not(p0)), nf(s0,p0))
  iff.syl(nf(s0,p0), nf(s0,not(p0)), or(forall(s0,p0),forall(s0,not(p0))))
  nf.def.3(s0, p0)
  iff.syl(or(forall(s0,p0),forall(s0,not(p0))), nf(s0,not(p0)), or(forall(s0,not(p0)),forall(s0,not(not(p0)))))
  nf.def.3(s0, not(p0))
  iff.syl(or(forall(s0,p0),forall(s0,not(p0))), or(forall(s0,not(p0)),forall(s0,not(not(p0)))), or(forall(s0,not(p0)),forall(s0,p0)))
  iff.or.com(forall(s0,p0), forall(s0,not(p0)))
  or.ifforii(forall(s0,not(p0)), forall(s0,not(p0)), forall(s0,p0), forall(s0,not(not(p0))))
  iff.id(forall(s0,not(p0)))
  a4igen.aaa.iff(s0, p0, not(not(p0)))
  iff.notnot(p0)
}
```

```follow
thm nf.noti(set s0, prop p0) {
  |- nf(s0, not(p0))
  -| nf(s0, p0)
} = {
  mp(nf(s0,not(p0)), nf(s0,p0))
  nf.not(s0, p0)
}
```

```follow
thm nf.notd(set s0, prop p0, prop p1) {
  |- imp(p1, nf(s0, not(p0)))
  -| imp(p1, nf(s0, p0))
} = {
  syl(p1, nf(s0,not(p0)), nf(s0,p0))
  nf.not(s0, p0)
}
```

```follow
thm nf.imp(set s0, prop p0, prop p1) {
  |- imp(and(nf(s0, p0), nf(s0,p1)), nf(s0, imp(p0, p1)))
} = {
  syl(and(nf(s0,p0),nf(s0,p1)), nf(s0,imp(p0,p1)), imp(exist(s0,imp(p0,p1)),forall(s0,imp(p0,p1))))
  nf.def.1.ext(s0, imp(p0,p1))
  rw23(and(nf(s0,p0),nf(s0,p1)), exist(s0,imp(p0,p1)), forall(s0,imp(p0,p1)), imp(forall(s0,p0),exist(s0,p1)), imp(exist(s0,p0),forall(s0,p1)))
  a4.aea(s0, p0, p1)
  a4.eae.1(s0, p0, p1)
  and.joini(nf(s0,p0), nf(s0,p1), imp(imp(forall(s0,p0),exist(s0,p1)),imp(exist(s0,p0),forall(s0,p1))))
  rw2(nf(s0,p0), nf(s0,p1), imp(imp(forall(s0,p0),exist(s0,p1)),imp(exist(s0,p0),forall(s0,p1))), imp(exist(s0,p1),forall(s0,p1)))
  nf.def.1.ext(s0, p1)
  syl(nf(s0,p0), imp(imp(exist(s0,p1),forall(s0,p1)),imp(imp(forall(s0,p0),exist(s0,p1)),imp(exist(s0,p0),forall(s0,p1)))), imp(exist(s0,p0),forall(s0,p0)))
  trans4.2(exist(s0,p0), forall(s0,p0), exist(s0,p1), forall(s0,p1))
  nf.def.1.ext(s0, p0)
}
```

```follow
thm nf.impii(set s0, prop p0, prop p1) {
  |- nf(s0, imp(p0, p1))
  -| nf(s0, p0)
  -| nf(s0, p1) 
} = {
  mp(nf(s0,imp(p0,p1)), and(nf(s0,p0),nf(s0,p1)))
  nf.imp(s0, p0, p1)
  and.introii(nf(s0,p0), nf(s0,p1))
}
```

```follow
thm nf.impd(set s0, prop p0, prop p1, prop p2) {
  |- imp(p2, nf(s0, imp(p0, p1)))
  -| imp(p2, nf(s0, p0))
  -| imp(p2, nf(s0,p1))
} = {
  syl(p2, nf(s0,imp(p0,p1)), and(nf(s0,p0),nf(s0,p1)))
  nf.imp(s0, p0, p1)
  and.introiid(p2, nf(s0,p0), nf(s0,p1))
}
```

```follow
thm nf.and(set s0, prop p0, prop p1) {
  |- imp(and(nf(s0, p0), nf(s0,p1)), nf(s0, and(p0, p1)))
} = {
  syl(and(nf(s0,p0),nf(s0,p1)), nf(s0,and(p0,p1)), nf(s0,not(imp(p0,not(p1)))))
  nf.iffnfi(s0, and(p0,p1), not(imp(p0,not(p1))))
  gen.forall(s0, iff(and(p0,p1),not(imp(p0,not(p1)))))
  iff.and.def(p0, p1)
  syl(and(nf(s0,p0),nf(s0,p1)), nf(s0,not(imp(p0,not(p1)))), nf(s0,imp(p0,not(p1))))
  nf.not(s0, imp(p0,not(p1)))
  syl(and(nf(s0,p0),nf(s0,p1)), nf(s0,imp(p0,not(p1))), and(nf(s0,p0),nf(s0,not(p1))))
  nf.imp(s0, p0, not(p1))
  and.2andii.1(nf(s0,p0), nf(s0,p1), nf(s0,p0), nf(s0,not(p1)))
  id(nf(s0,p0))
  nf.not(s0, p1)
}
```

```follow
thm nf.andi(set s0, prop p0, prop p1) {
  |- nf(s0, and(p0, p1))
  -| nf(s0, p0)
  -| nf(s0, p1) 
} = {
  mp(nf(s0,and(p0,p1)), and(nf(s0,p0),nf(s0,p1)))
  nf.and(s0, p0, p1)
  and.introii(nf(s0,p0), nf(s0,p1))
}
```

```follow
thm nf.andd(set s0, prop p0, prop p1, prop p2) {
  |- imp(p2, nf(s0, and(p0, p1)))
  -| imp(p2, nf(s0, p0))
  -| imp(p2, nf(s0,p1))
} = {
  syl(p2, nf(s0,and(p0,p1)), and(nf(s0,p0),nf(s0,p1)))
  nf.and(s0, p0, p1)
  and.introiid(p2, nf(s0,p0), nf(s0,p1))
}
```

## `nf` 与 `or`

```follow
thm nf.or(set s0, prop p0, prop p1) {
  |- imp(and(nf(s0, p0), nf(s0,p1)), nf(s0, or(p0, p1)))
} = {
  syl(and(nf(s0,p0),nf(s0,p1)), nf(s0,or(p0,p1)), nf(s0,imp(not(p0),p1)))
  nf.iffnfigen(s0, imp(not(p0),p1), or(p0,p1))
  iff.or.def(p0, p1)
  syl(and(nf(s0,p0),nf(s0,p1)), nf(s0,imp(not(p0),p1)), and(nf(s0,not(p0)),nf(s0,p1)))
  nf.imp(s0, not(p0), p1)
  and.2andii.1(nf(s0,p0), nf(s0,p1), nf(s0,not(p0)), nf(s0,p1))
  nf.not(s0, p0)
  id(nf(s0,p1))
}
```

```follow
thm nf.ori(set s0, prop p0, prop p1) {
  |- nf(s0, or(p0, p1))
  -| nf(s0, p0)
  -| nf(s0, p1) 
} = {
  mp(nf(s0,or(p0,p1)), and(nf(s0,p0),nf(s0,p1)))
  nf.or(s0, p0, p1)
  and.introii(nf(s0,p0), nf(s0,p1))
}
```

```follow
thm nf.ord(set s0, prop p0, prop p1, prop p2) {
  |- imp(p2, nf(s0, or(p0, p1)))
  -| imp(p2, nf(s0, p0))
  -| imp(p2, nf(s0, p1))
} = {
  syl(p2, nf(s0,or(p0,p1)), and(nf(s0,p0),nf(s0,p1)))
  nf.or(s0, p0, p1)
  and.introiid(p2, nf(s0,p0), nf(s0,p1))
}
```

## `nf` 与 `iff` 

```follow
thm nf.iff(set s0, prop p0, prop p1) {
  |- imp(and(nf(s0, p0), nf(s0,p1)), nf(s0, iff(p0, p1)))
} = {
  syl(and(nf(s0,p0),nf(s0,p1)), nf(s0,iff(p0,p1)), nf(s0,and(imp(p0,p1),imp(p1,p0))))
  nf.iffnfigen(s0, and(imp(p0,p1),imp(p1,p0)), iff(p0,p1))
  iff.def.iff(p0, p1)
  syl(and(nf(s0,p0),nf(s0,p1)), nf(s0,and(imp(p0,p1),imp(p1,p0))), and(nf(s0,imp(p0,p1)),nf(s0,imp(p1,p0))))
  nf.and(s0, imp(p0,p1), imp(p1,p0))
  and.introiid(and(nf(s0,p0),nf(s0,p1)), nf(s0,imp(p0,p1)), nf(s0,imp(p1,p0)))
  nf.imp(s0, p0, p1)
  syl(and(nf(s0,p0),nf(s0,p1)), nf(s0,imp(p1,p0)), and(nf(s0,p1),nf(s0,p0)))
  nf.imp(s0, p1, p0)
  and.com(nf(s0,p0), nf(s0,p1))
}
```

```follow
thm nf.iffii(set s0, prop p0, prop p1) {
  |- nf(s0, iff(p0, p1))
  -| nf(s0, p0)
  -| nf(s0, p1)
} = {
  mp(nf(s0,iff(p0,p1)), and(nf(s0,p0),nf(s0,p1)))
  nf.iff(s0, p0, p1)
  and.introii(nf(s0,p0), nf(s0,p1))
}
```

```follow
thm nf.iffd(set s0, prop p0, prop p1, prop p2) {
  |- imp(p2, nf(s0, iff(p0, p1)))
  -| imp(p2, nf(s0, p0))
  -| imp(p2, nf(s0, p1))
} = {
  syl(p2, nf(s0,iff(p0,p1)), and(nf(s0,p0),nf(s0,p1)))
  nf.iff(s0, p0, p1)
  and.introiid(p2, nf(s0,p0), nf(s0,p1))
}
```

## `nf` 与 `eq`

```follow
thm nf.eqid(set s0, set s1) {
  |- nf(s0, eq(c(s1), c(s1)))
} = {
  nf.gen(s0, eq(c(s1),c(s1)))
  eq.id(s1)
}
```


