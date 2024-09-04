
# 逻辑连接符 `iff` 

在一阶逻辑中，两个命题等价的英文是 `If-And-Only-If`。这一小节就是介绍这个逻辑关系的。

```follow
term prop iff(prop p0, prop p1) { (p0 ↔ p1) }
```

```follow
axiom iff.def(prop p0, prop p1) {
  |- imp(iff(p0,p1), and(imp(p0,p1),imp(p1,p0)))
  |- imp(and(imp(p0,p1),imp(p1,p0)), iff(p0,p1))
}
```

## 真值表 

| 名字 | 第一组值 | 第二组值 | 第三组值 | 第四组值 | 
| :---: | :---: | :---: | :---: | :---: |
| `p0` | 0 | 0 | 1 | 1 | 
| `p1` | 0 | 1 | 0 | 1 |
| `p0→p1` | 1 | 1 | 0 | 1 | 
| `p1→p0` | 1 | 0 | 1 | 1 |
| `(p0→p1)∧(p1→p0)` | 1 | 0 | 0 | 1 | 

## 消去 `Elimination` 

```follow
thm iff.left(prop p0, prop p1) {
  |- imp(iff(p0,p1),imp(p0,p1))
} = {
  syl(iff(p0,p1), imp(p0,p1), and(imp(p0,p1),imp(p1,p0)))
  iff.def(p0, p1)
  and.left(imp(p0,p1), imp(p1,p0))
}
```

```follow
thm iff.lefti(prop p0, prop p1) {
  |- imp(p0, p1)
  -| iff(p0, p1)
} = {
  mp(imp(p0,p1), iff(p0,p1))
  iff.left(p0, p1)
}
```

```follow
thm iff.leftid(prop p0, prop p1, prop p2) {
  |- imp(p0, imp(p1, p2))
  -| imp(p0, iff(p1, p2))
} = {
  syl(p0, imp(p1,p2), iff(p1,p2))
  iff.left(p1, p2)
}
```

```follow
thm iff.right(prop p0, prop p1) {
  |- imp(iff(p0,p1), imp(p1,p0))
} = {
  syl(iff(p0,p1), imp(p1,p0), and(imp(p0,p1),imp(p1,p0)))
  iff.def(p0, p1)
  and.right(imp(p0,p1), imp(p1,p0))
}
```

```follow
thm iff.righti(prop p0, prop p1) {
  |- imp(p0, p1)
  -| iff(p1, p0)
} = {
  mp(imp(p0,p1), iff(p1,p0))
  iff.right(p1, p0)
}
```

```follow
thm iff.rightid(prop p0, prop p1, prop p2) {
  |- imp(p0, imp(p1, p2))
  -| imp(p0, iff(p2, p1))
} = {
  syl(p0, imp(p1,p2), iff(p2,p1))
  iff.right(p2, p1)
}
```

## 引入，`Introduction` 

```follow
thm iff.intro.1(prop p0, prop p1) {
  |- imp(imp(p0,p1),imp(imp(p1,p0),iff(p0,p1)))
  |- imp(imp(p1,p0),imp(imp(p0,p1),iff(p0,p1)))
} = {
  com12i(imp(p1,p0), imp(p0,p1), iff(p0,p1))
  rw3(imp(p0,p1), imp(p1,p0), iff(p0,p1), and(imp(p0,p1),imp(p1,p0)))
  and.intro(imp(p0,p1), imp(p1,p0))
  iff.def(p0, p1)
}
```

```follow
thm iff.introii.1(prop p0, prop p1) {
  |- iff(p0, p1)
  -| imp(p0, p1)
  -| imp(p1, p0)
} = {
  mp(iff(p0,p1), imp(p0,p1))
  mp(imp(imp(p0,p1),iff(p0,p1)), imp(p1,p0))
  iff.intro.1(p0, p1)
}
```

```follow
thm iff.introiid.1(prop p0, prop p1, prop p2) {
  |- imp(p0, iff(p1, p2))
  -| imp(p0, imp(p1, p2))
  -| imp(p0, imp(p2, p1))
} = {
  mpd(p0, iff(p1,p2), imp(p1,p2))
  syl(p0, imp(imp(p1,p2),iff(p1,p2)), imp(p2,p1))
  iff.intro.1(p1, p2)
}
```

```follow
thm iff.intro.2(prop p0, prop p1) {
  |- imp(p0, imp(p1, iff(p0, p1)))
  |- imp(p1, imp(p0, iff(p0, p1)))
} = {
  com12i(p1, p0, iff(p0,p1))
  and.spliti(p0, p1, iff(p0,p1))
  iff.introiid.1(and(p0,p1), p0, p1)
  syl(and(p0,p1), imp(p0,p1), p1)
  and.right(p0, p1)
  a1(p1, p0)
  syl(and(p0,p1), imp(p1,p0), p0)
  and.left(p0, p1)
  a1(p0, p1)
}
```

```follow
thm iff.introii.2(prop p0, prop p1) {
  |- iff(p0, p1)
  -| p0
  -| p1
} = {
  mp(iff(p0,p1), p0)
  mp(imp(p0,iff(p0,p1)), p1)
  iff.intro.2(p0, p1)
}
```

```follow
thm iff.introiid.2(prop p0, prop p1, prop p2) {
  |- imp(p0, iff(p1, p2))
  -| imp(p0, p1)
  -| imp(p0, p2)
} = {
  mpd(p0, iff(p1,p2), p1)
  syl(p0, imp(p1,iff(p1,p2)), p2)
  iff.intro.2(p1, p2)
}
```

## 交换律

```follow
thm iff.com(prop p0, prop p1) {
  |- iff(iff(p0,p1), iff(p1,p0))
  |- imp(iff(p0,p1), iff(p1,p0))
} = {
  iff.introii.1(iff(p0,p1), iff(p1,p0))

  syl(iff(p0,p1), iff(p1,p0), and(imp(p0,p1),imp(p1,p0)))
  iff.def(p0, p1)
  syl(and(imp(p0,p1),imp(p1,p0)), iff(p1,p0), and(imp(p1,p0),imp(p0,p1)))
  iff.def(p1, p0)
  and.com(imp(p0,p1), imp(p1,p0))

  syl(iff(p1,p0), iff(p0,p1), and(imp(p1,p0),imp(p0,p1)))
  iff.def(p1, p0)
  syl(and(imp(p1,p0),imp(p0,p1)), iff(p0,p1), and(imp(p0,p1),imp(p1,p0)))
  iff.def(p0, p1)
  and.com(imp(p1,p0), imp(p0,p1))
}
```

```follow
thm iff.comi(prop p0, prop p1) {
  |- iff(p0, p1)
  -| iff(p1, p0)
} = {
  mp(iff(p0,p1), iff(p1,p0))
  iff.com(p1, p0)
}
```

```follow
thm iff.comid(prop p0, prop p1, prop p2) {
  |- imp(p0, iff(p1, p2))
  -| imp(p0, iff(p2, p1))
} = {
  syl(p0, iff(p1,p2), iff(p2,p1))
  iff.com(p2, p1)
}
```

## Identity

```follow
thm iff.id(prop p0) {
  |- iff(p0, p0)
} = {
  iff.introii.1(p0, p0)
  id(p0)
}
```

```follow
thm iff.idd(prop p0, prop p1) {
  |- imp(p0, iff(p1, p1))
} = {
  a1i(p0, iff(p1,p1))
  iff.id(p1)
}
```

```follow
thm iff.iid.1(prop p0, prop p1) {
  |- imp(p0, p1)
  -| imp(p0, iff(p1, p0))
}= {
  iid(p0, p1)
  iff.rightid(p0, p0, p1)
}
```

```follow
thm iff.iid.2(prop p0, prop p1) {
  |- imp(p0, p1)
  -| imp(p0, iff(p0, p1))
}= {
  iid(p0, p1)
  iff.leftid(p0, p0, p1)
}
```

## 传递性 `Transition`

```follow
thm iff.trans.1(prop p0, prop p1, prop p2) {
  |- imp(iff(p0, p1), imp(iff(p1, p2), iff(p0, p2)))
} = {
  rw23(iff(p0,p1), iff(p1,p2), iff(p0,p2), and(imp(p1,p2),imp(p2,p1)), and(imp(p0,p2),imp(p2,p0)))
  iff.def(p1, p2)
  iff.def(p0, p2)
  and.2andiid.1(iff(p0,p1), imp(p1,p2), imp(p2,p1), imp(p0,p2), imp(p2,p0))
  transid.1(p2, p1, p0, iff(p0,p1))
  iff.right(p0, p1)
  transid.2(p0, p1, p2, iff(p0,p1))
  iff.left(p0, p1)
}
```

```follow
thm iff.trans.2(prop p0, prop p1, prop p2) {
  |- imp(iff(p0, p1), imp(iff(p2, p1), iff(p0, p2)))
  |- imp(iff(p0, p1), imp(iff(p1, p2), iff(p2, p0)))
  |- imp(iff(p0, p1), imp(iff(p2, p1), iff(p2, p0)))
  |- imp(iff(p1, p2), imp(iff(p0, p1), iff(p0, p2)))
  |- imp(iff(p1, p2), imp(iff(p1, p0), iff(p0, p2)))
  |- imp(iff(p1, p2), imp(iff(p0, p1), iff(p2, p0)))
  |- imp(iff(p1, p2), imp(iff(p1, p0), iff(p2, p0)))
} = {
  rw2(iff(p1,p2), iff(p1,p0), iff(p2,p0), iff(p0,p1))
  rw3(iff(p1,p2), iff(p0,p1), iff(p2,p0), iff(p0,p2))
  rw2(iff(p1,p2), iff(p1,p0), iff(p0,p2), iff(p0,p1))
  com12i(iff(p1,p2), iff(p0,p1), iff(p0,p2))
  rw3(iff(p0,p1), iff(p2,p1), iff(p2,p0), iff(p0,p2))
  rw3(iff(p0,p1), iff(p1,p2), iff(p2,p0), iff(p0,p2))
  rw2(iff(p0,p1), iff(p2,p1), iff(p0,p2), iff(p1,p2))
  iff.com(p2, p1)
  iff.com(p0, p2)
  iff.com(p1, p0)
  iff.trans.1(p0, p1, p2)
}
```

```follow
thm iff.trans.3(prop p0, prop p1, prop p2) {
  |- imp(iff(p0, p1), iff(iff(p1, p2), iff(p0, p2)))
  |- imp(iff(p0, p1), iff(iff(p0, p2), iff(p1, p2)))
  |- imp(iff(p0, p1), iff(iff(p1, p2), iff(p2, p0)))
  |- imp(iff(p0, p1), iff(iff(p0, p2), iff(p2, p1)))
  |- imp(iff(p0, p1), iff(iff(p2, p1), iff(p0, p2)))
  |- imp(iff(p0, p1), iff(iff(p2, p0), iff(p1, p2)))
  |- imp(iff(p0, p1), iff(iff(p2, p1), iff(p2, p0)))
  |- imp(iff(p0, p1), iff(iff(p2, p0), iff(p2, p1)))
} = {
  iff.introiid.1(iff(p0,p1), iff(p1,p2), iff(p0,p2))
  iff.introiid.1(iff(p0,p1), iff(p0,p2), iff(p1,p2))
  iff.introiid.1(iff(p0,p1), iff(p1,p2), iff(p2,p0))
  iff.trans.1(p0, p1, p2)
  iff.introiid.1(iff(p0,p1), iff(p0,p2), iff(p2,p1))
  iff.introiid.1(iff(p0,p1), iff(p2,p1), iff(p0,p2))
  iff.introiid.1(iff(p0,p1), iff(p2,p0), iff(p1,p2))
  iff.introiid.1(iff(p0,p1), iff(p2,p1), iff(p2,p0))
  iff.introiid.1(iff(p0,p1), iff(p2,p0), iff(p2,p1))
  iff.trans.2(p0, p1, p2)
  iff.trans.2(p2, p0, p1)
}
```

```follow
thm iff.transi.1(prop p0, prop p1, prop p2) {
  |- imp(iff(p1, p2), iff(p0, p2))
  |- imp(iff(p0, p2), iff(p1, p2))
  |- imp(iff(p1, p2), iff(p2, p0))
  |- imp(iff(p0, p2), iff(p2, p1))
  |- imp(iff(p2, p1), iff(p0, p2))
  |- imp(iff(p2, p0), iff(p1, p2))
  |- imp(iff(p2, p1), iff(p2, p0))
  |- imp(iff(p2, p0), iff(p2, p1))
  -| iff(p0, p1)
} = {
  mp(imp(iff(p1,p2),iff(p0,p2)), iff(p0,p1))
  mp(imp(iff(p0,p2),iff(p1,p2)), iff(p0,p1))
  mp(imp(iff(p1,p2),iff(p2,p0)), iff(p0,p1))
  mp(imp(iff(p0,p2),iff(p2,p1)), iff(p0,p1))
  mp(imp(iff(p2,p1),iff(p0,p2)), iff(p0,p1))
  mp(imp(iff(p2,p0),iff(p1,p2)), iff(p0,p1))
  mp(imp(iff(p2,p1),iff(p2,p0)), iff(p0,p1))
  mp(imp(iff(p2,p0),iff(p2,p1)), iff(p0,p1))
  iff.trans.1(p0, p1, p2)
  iff.trans.2(p0, p1, p2)
  iff.trans.2(p2, p0, p1)
}
```

```follow
thm iff.transid.1(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p3, imp(iff(p1, p2), iff(p0, p2)))
  |- imp(p3, imp(iff(p0, p2), iff(p1, p2)))
  |- imp(p3, imp(iff(p1, p2), iff(p2, p0)))
  |- imp(p3, imp(iff(p0, p2), iff(p2, p1)))
  |- imp(p3, imp(iff(p2, p1), iff(p0, p2)))
  |- imp(p3, imp(iff(p2, p0), iff(p1, p2)))
  |- imp(p3, imp(iff(p2, p1), iff(p2, p0)))
  |- imp(p3, imp(iff(p2, p0), iff(p2, p1)))
  -| imp(p3, iff(p0, p1))
} = {
  syl(p3, imp(iff(p1,p2),iff(p0,p2)), iff(p0,p1))
  syl(p3, imp(iff(p0,p2),iff(p1,p2)), iff(p0,p1))
  syl(p3, imp(iff(p1,p2),iff(p2,p0)), iff(p0,p1))
  syl(p3, imp(iff(p0,p2),iff(p2,p1)), iff(p0,p1))
  syl(p3, imp(iff(p2,p1),iff(p0,p2)), iff(p0,p1))
  syl(p3, imp(iff(p2,p0),iff(p1,p2)), iff(p0,p1))
  syl(p3, imp(iff(p2,p1),iff(p2,p0)), iff(p0,p1))
  syl(p3, imp(iff(p2,p0),iff(p2,p1)), iff(p0,p1))
  iff.trans.1(p0, p1, p2)
  iff.trans.2(p0, p1, p2)
  iff.trans.2(p2, p0, p1)
}
```

```follow
thm iff.transi.2(prop p0, prop p1, prop p2) {
  |- iff(iff(p1, p2), iff(p0, p2))
  |- iff(iff(p0, p2), iff(p1, p2))
  |- iff(iff(p1, p2), iff(p2, p0))
  |- iff(iff(p0, p2), iff(p2, p1))
  |- iff(iff(p2, p1), iff(p0, p2))
  |- iff(iff(p2, p0), iff(p1, p2))
  |- iff(iff(p2, p1), iff(p2, p0))
  |- iff(iff(p2, p0), iff(p2, p1))
  -| iff(p0, p1)
} = {
  mp(iff(iff(p1,p2),iff(p0,p2)), iff(p0,p1))
  mp(iff(iff(p0,p2),iff(p1,p2)), iff(p0,p1))
  mp(iff(iff(p1,p2),iff(p2,p0)), iff(p0,p1))
  mp(iff(iff(p0,p2),iff(p2,p1)), iff(p0,p1))
  mp(iff(iff(p2,p1),iff(p0,p2)), iff(p0,p1))
  mp(iff(iff(p2,p0),iff(p1,p2)), iff(p0,p1))
  mp(iff(iff(p2,p1),iff(p2,p0)), iff(p0,p1))
  mp(iff(iff(p2,p0),iff(p2,p1)), iff(p0,p1))
  iff.trans.3(p0, p1, p2)
}
```

```follow
thm iff.transid.2(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p3, iff(iff(p1, p2), iff(p0, p2)))
  |- imp(p3, iff(iff(p0, p2), iff(p1, p2)))
  |- imp(p3, iff(iff(p1, p2), iff(p2, p0)))
  |- imp(p3, iff(iff(p0, p2), iff(p2, p1)))
  |- imp(p3, iff(iff(p2, p1), iff(p0, p2)))
  |- imp(p3, iff(iff(p2, p0), iff(p1, p2)))
  |- imp(p3, iff(iff(p2, p1), iff(p2, p0)))
  |- imp(p3, iff(iff(p2, p0), iff(p2, p1)))
  -| imp(p3, iff(p0, p1))
} = {
  syl(p3, iff(iff(p1,p2),iff(p0,p2)), iff(p0,p1))
  syl(p3, iff(iff(p0,p2),iff(p1,p2)), iff(p0,p1))
  syl(p3, iff(iff(p1,p2),iff(p2,p0)), iff(p0,p1))
  syl(p3, iff(iff(p0,p2),iff(p2,p1)), iff(p0,p1))
  syl(p3, iff(iff(p2,p1),iff(p0,p2)), iff(p0,p1))
  syl(p3, iff(iff(p2,p0),iff(p1,p2)), iff(p0,p1))
  syl(p3, iff(iff(p2,p1),iff(p2,p0)), iff(p0,p1))
  syl(p3, iff(iff(p2,p0),iff(p2,p1)), iff(p0,p1))
  iff.trans.3(p0, p1, p2)
}
```

## 三段论 `syllogism` 

```follow
thm iff.syl(prop p0, prop p1, prop p2) {
  |- iff(p0, p1)
  -| iff(p0, p2)
  -| iff(p2, p1)
} = {
  mp(iff(p0,p1), iff(p0,p2))
  iff.transi.1(p2, p1, p0)
}
```

```follow
thm iff.syld(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p0, iff(p1, p2))
  -| imp(p0, iff(p1, p3))
  -| imp(p0, iff(p3, p2))
} = {
  mpd(p0, iff(p1,p2), iff(p1,p3))
  iff.transid.1(p3, p2, p1, p0)
}
```

## 替换某一个命题, `rewrite`

```follow
thm iff.rw2(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p0, iff(p1, p2))
  -| imp(p0, iff(p3, p2))
  -| iff(p1, p3)
} = {
  syl(p0, iff(p1,p2), iff(p3,p2))
  iff.transi.1(p1, p3, p2)
}
```

```follow
thm iff.rw3(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p0, iff(p1, p2))
  -| imp(p0, iff(p1, p3))
  -| iff(p2, p3)
} = {
  syl(p0, iff(p1,p2), iff(p1,p3))
  iff.transi.1(p2, p3, p1)
}
```

```follow
thm iff.rw23(prop p0, prop p1, prop p2, prop p3, prop p4) {
  |- imp(p0, iff(p1, p2))
  -| imp(p0, iff(p3, p4))
  -| iff(p1, p3)
  -| iff(p2, p4)
} = {
  iff.rw2(p0, p1, p2, p3)
  iff.rw3(p0, p3, p2, p4)
}
```

## 复合定理 `imp.iffimp`

```follow
thm imp.iffimp.1(prop p0, prop p1, prop p2) {
  |- imp(imp(p0,iff(p1,p2)), iff(imp(p0,p1),imp(p0,p2)))
} = {
  iff.introiid.1(imp(p0,iff(p1,p2)), imp(p0,p1), imp(p0,p2))
  a2id(imp(p0,iff(p1,p2)), p0, p1, p2)
  transi.1(p0, iff(p1,p2), imp(p1,p2))
  iff.left(p1, p2)
  a2id(imp(p0,iff(p1,p2)), p0, p2, p1)
  transi.1(p0, iff(p1,p2), imp(p2,p1))
  iff.right(p1, p2)
}
```

```follow
thm imp.iffimpi.1(prop p0, prop p1, prop p2) {
  |- iff(imp(p0,p1),imp(p0,p2))
  -| imp(p0,iff(p1,p2)) 
} = {
  mp(iff(imp(p0,p1),imp(p0,p2)), imp(p0,iff(p1,p2)))
  imp.iffimp.1(p0, p1, p2)
}
```

```follow
thm imp.iffimpid.1(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p3, iff(imp(p0,p1),imp(p0,p2)))
  -| imp(p3, imp(p0,iff(p1,p2)))
} = {
  syl(p3, iff(imp(p0,p1),imp(p0,p2)), imp(p0,iff(p1,p2)))
  imp.iffimp.1(p0, p1, p2)
}
```

```follow
thm imp.iffimp.2(prop p0, prop p1, prop p2) {
  |- imp(imp(p0,iff(p2,p1)), iff(imp(p0,p1),imp(p0,p2)))
} = {
  syl(imp(p0,iff(p2,p1)), iff(imp(p0,p1),imp(p0,p2)), imp(p0,iff(p1,p2)))
  imp.iffimp.1(p0, p1, p2)
  a2i(p0, iff(p2,p1), iff(p1,p2))
  a1i(p0, imp(iff(p2,p1),iff(p1,p2)))
  iff.com(p2, p1)
}
```

```follow
thm imp.iffimpi.2(prop p0, prop p1, prop p2) {
  |- iff(imp(p0,p1),imp(p0,p2))
  -| imp(p0, iff(p2, p1))
} = {
  mp(iff(imp(p0,p1),imp(p0,p2)), imp(p0,iff(p2,p1)))
  imp.iffimp.2(p0, p1, p2)
}
```

```follow
thm imp.iffimpid.2(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p3, iff(imp(p0,p1),imp(p0,p2)))
  -| imp(p3, imp(p0, iff(p2, p1)))
} = {
  syl(p3, iff(imp(p0,p1),imp(p0,p2)), imp(p0,iff(p2,p1)))
  imp.iffimp.2(p0, p1, p2)
}
```

```follow
thm imp.iffimp.3(prop p0, prop p1, prop p2, prop p3) {
  |- imp(iff(p0,p1),imp(iff(p2,p3),iff(imp(p0,p2),imp(p1,p3))))
  |- imp(iff(p2,p3),imp(iff(p0,p1),iff(imp(p0,p2),imp(p1,p3))))
  |- imp(and(iff(p0,p1),iff(p2,p3)),iff(imp(p0,p2),imp(p1,p3)))
} = {
  com12i(iff(p2,p3), iff(p0,p1), iff(imp(p0,p2),imp(p1,p3)))
  and.spliti(iff(p0,p1), iff(p2,p3), iff(imp(p0,p2),imp(p1,p3)))
  iff.introiid.1(and(iff(p0,p1),iff(p2,p3)), imp(p0,p2), imp(p1,p3))
  syl(and(iff(p0,p1),iff(p2,p3)), imp(imp(p0,p2),imp(p1,p3)), and(imp(p1,p0),imp(p2,p3)))
  and.2andii.1(iff(p0,p1), iff(p2,p3), imp(p1,p0), imp(p2,p3))
  iff.right(p0, p1)
  iff.left(p2, p3)
  and.joini(imp(p1,p0), imp(p2,p3), imp(imp(p0,p2),imp(p1,p3)))
  trans4.2(p1, p0, p2, p3)
  syl(and(iff(p0,p1),iff(p2,p3)), imp(imp(p1,p3),imp(p0,p2)), and(imp(p0,p1),imp(p3,p2)))
  and.2andii.1(iff(p0,p1), iff(p2,p3), imp(p0,p1), imp(p3,p2))
  iff.left(p0, p1)
  iff.right(p2, p3)
  and.joini(imp(p0,p1), imp(p3,p2), imp(imp(p1,p3),imp(p0,p2)))
  trans4.2(p0, p1, p3, p2)
}
```

```follow
thm imp.iffimpii.3(prop p0, prop p1, prop p2, prop p3) {
  |- iff(imp(p0,p1),imp(p2,p3))
  -| iff(p0, p2)
  -| iff(p1, p3)
} = {
  mp(iff(imp(p0,p1),imp(p2,p3)), iff(p0,p2))
  mp(imp(iff(p0,p2),iff(imp(p0,p1),imp(p2,p3))), iff(p1,p3))
  imp.iffimp.3(p0, p2, p1, p3)
}
```


```follow
thm imp.iffimpiid.3(prop p0, prop p1, prop p2, prop p3, prop p4) {
  |- imp(p0, iff(imp(p1,p2),imp(p3,p4)))
  -| imp(p0, iff(p1, p3))
  -| imp(p0, iff(p2, p4))
} = {
  mpd(p0, iff(imp(p1,p2),imp(p3,p4)), iff(p1,p3))
  syl(p0, imp(iff(p1,p3),iff(imp(p1,p2),imp(p3,p4))), iff(p2,p4))
  imp.iffimp.3(p1, p3, p2, p4)
}
```

```follow
thm imp.iffimp.4(prop p0, prop p1, prop p2) {
  |- imp(iff(p1, p2), iff(imp(p0, p1), imp(p0, p2)))
} = {
  mp(imp(iff(p1,p2),iff(imp(p0,p1),imp(p0,p2))), iff(p0,p0))
  imp.iffimp.3(p0, p0, p1, p2)
  iff.id(p0)
}
```


```follow
thm imp.iffimpi.4(prop p0, prop p1, prop p2) {
  |- iff(imp(p0, p1), imp(p0, p2))
  -| iff(p1, p2)
} = {
  mp(iff(imp(p0,p1),imp(p0,p2)), iff(p1,p2))
  imp.iffimp.4(p0, p1, p2)
}
```

```follow
thm imp.iffimpd.4(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p0, iff(imp(p1, p2), imp(p1, p3)))
  -| imp(p0, iff(p2, p3))
} = {
  syl(p0, iff(imp(p1,p2),imp(p1,p3)), iff(p2,p3))
  imp.iffimp.4(p1, p2, p3)
}
```

```follow
thm imp.iffimp.5(prop p0, prop p1, prop p2) {
  |- imp(iff(p1, p2), iff(imp(p1, p0), imp(p2, p0)))
} = {
  mp(imp(iff(p1,p2),iff(imp(p1,p0),imp(p2,p0))), iff(p0,p0))
  imp.iffimp.3(p1, p2, p0, p0)
  iff.id(p0)
}
```

```follow
thm imp.iffimpi.5(prop p0, prop p1, prop p2) {
  |- iff(imp(p1, p0), imp(p2, p0))
  -| iff(p1, p2)
} = {
  mp(iff(imp(p1,p0),imp(p2,p0)), iff(p1,p2))
  imp.iffimp.5(p0, p1, p2)
}
```

```follow
thm imp.iffimpd.5(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p0, iff(imp(p2, p1), imp(p3, p1)))
  -| imp(p0, iff(p2, p3))
} = {
  syl(p0, iff(imp(p2,p1),imp(p3,p1)), iff(p2,p3))
  imp.iffimp.5(p1, p2, p3)
}
```

```follow
thm imp.iffimp.6(prop p0, prop p1, prop p2) {
  |- iff(imp(p0, iff(p1, p2)), iff(imp(p0, p1), imp(p0, p2)))
  |- iff(iff(imp(p0, p1), imp(p0, p2)), imp(p0, iff(p1, p2)))
  |- imp(imp(p0, iff(p1, p2)), iff(imp(p0, p1), imp(p0, p2)))
  |- imp(iff(imp(p0, p1), imp(p0, p2)), imp(p0, iff(p1, p2)))
} = {
  iff.comi(iff(imp(p0,p1),imp(p0,p2)), imp(p0,iff(p1,p2)))
  iff.lefti(imp(p0,iff(p1,p2)), iff(imp(p0,p1),imp(p0,p2)))
  iff.righti(iff(imp(p0,p1),imp(p0,p2)), imp(p0,iff(p1,p2)))

  iff.introii.1(imp(p0,iff(p1,p2)), iff(imp(p0,p1),imp(p0,p2)))
  imp.iffimp.1(p0, p1, p2)

  and.spliti(iff(imp(p0,p1),imp(p0,p2)), p0, iff(p1,p2))
  iff.introiid.1(and(iff(imp(p0,p1),imp(p0,p2)),p0), p1, p2)
  and.joini(iff(imp(p0,p1),imp(p0,p2)), p0, imp(p1,p2))
  com12id(iff(imp(p0,p1),imp(p0,p2)), p0, p1, p2)
  rw2(iff(imp(p0,p1),imp(p0,p2)), p1, imp(p0,p2), imp(p0,p1))
  a1(p1, p0)
  iff.left(imp(p0,p1), imp(p0,p2))

  and.joini(iff(imp(p0,p1),imp(p0,p2)), p0, imp(p2,p1))
  com12id(iff(imp(p0,p1),imp(p0,p2)), p0, p2, p1)
  rw2(iff(imp(p0,p1),imp(p0,p2)), p2, imp(p0,p1), imp(p0,p2))
  a1(p2, p0)
  iff.right(imp(p0,p1), imp(p0,p2))
}
```

```follow
thm imp.iffimpi.6(prop p0, prop p1, prop p2) {
  |- imp(p0, iff(p1, p2)) 
  -| iff(imp(p0, p1), imp(p0, p2)))
} = {
  mp(imp(p0,iff(p1,p2)), iff(imp(p0,p1),imp(p0,p2)))
  imp.iffimp.6(p0, p1, p2)
}
```

## 复合定理 `iff.2iff`

```follow
thm iff.2iff.1(prop p0, prop p1, prop p2, prop p3) {
  |- imp(
    imp(imp(p0,p1),imp(p2,p3)),
    imp(imp(imp(p1,p0),imp(p3,p2)),
      imp(iff(p0, p1), iff(p2, p3))
    )
  )
  |- imp(
    imp(imp(p1,p0),imp(p3,p2)),
    imp(imp(imp(p0,p1),imp(p2,p3)),
      imp(iff(p0, p1), iff(p2, p3))
    )
  )
  |- imp(and(imp(imp(p0,p1),imp(p2,p3)), 
    imp(imp(p1,p0),imp(p3,p2))), 
    imp(iff(p0, p1), iff(p2, p3)))
  |- imp(and(imp(imp(p1,p0),imp(p3,p2)),
    imp(imp(p0,p1),imp(p2,p3))), 
    imp(iff(p0, p1), iff(p2, p3)))
} = {
  and.spliti(imp(imp(p0,p1),imp(p2,p3)), imp(imp(p1,p0),imp(p3,p2)), imp(iff(p0,p1),iff(p2,p3)))
  and.spliti(imp(imp(p1,p0),imp(p3,p2)), imp(imp(p0,p1),imp(p2,p3)), imp(iff(p0,p1),iff(p2,p3)))
  syl(and(imp(imp(p1,p0),imp(p3,p2)),imp(imp(p0,p1),imp(p2,p3))), imp(iff(p0,p1),iff(p2,p3)), and(imp(imp(p0,p1),imp(p2,p3)),imp(imp(p1,p0),imp(p3,p2))))
  and.com(imp(imp(p1,p0),imp(p3,p2)), imp(imp(p0,p1),imp(p2,p3)))
  rw23(and(imp(imp(p0,p1),imp(p2,p3)),imp(imp(p1,p0),imp(p3,p2))), iff(p0,p1), iff(p2,p3), and(imp(p0,p1),imp(p1,p0)), and(imp(p2,p3),imp(p3,p2)))
  iff.def(p0, p1)
  iff.def(p2, p3)
  and.2andiid.1(and(imp(imp(p0,p1),imp(p2,p3)),imp(imp(p1,p0),imp(p3,p2))), imp(p0,p1), imp(p1,p0), imp(p2,p3), imp(p3,p2))
  and.left(imp(imp(p0,p1),imp(p2,p3)), imp(imp(p1,p0),imp(p3,p2)))
  and.right(imp(imp(p0,p1),imp(p2,p3)), imp(imp(p1,p0),imp(p3,p2)))
}
```

```follow
thm iff.2iffii.1(prop p0, prop p1, prop p2, prop p3) {
  |- imp(iff(p0, p1), iff(p2, p3))
  -| imp(imp(p0,p1),imp(p2,p3))
  -| imp(imp(p1,p0),imp(p3,p2))
} = {
  mp(imp(iff(p0,p1),iff(p2,p3)), imp(imp(p0,p1),imp(p2,p3)))
  mp(imp(imp(imp(p0,p1),imp(p2,p3)),imp(iff(p0,p1),iff(p2,p3))), imp(imp(p1,p0),imp(p3,p2)))
  iff.2iff.1(p0, p1, p2, p3)
}
```

```follow
thm iff.2iffiid(prop p0, prop p1, prop p2, prop p3, prop p4) {
  |- imp(p0, imp(iff(p1, p2), iff(p3, p4)))
  -| imp(p0, imp(imp(p1,p2),imp(p3,p4)))
  -| imp(p0, imp(imp(p2,p1),imp(p4,p3)))
} = {
  mpd(p0, imp(iff(p1,p2),iff(p3,p4)), imp(imp(p1,p2),imp(p3,p4)))
  syl(p0, imp(imp(imp(p1,p2),imp(p3,p4)),imp(iff(p1,p2),iff(p3,p4))), imp(imp(p2,p1),imp(p4,p3)))
  iff.2iff.1(p1, p2, p3, p4)
}
```

```follow
thm iff.2iff.2(prop p0, prop p1, prop p2, prop p3) {
  |- imp(iff(p0,p2), imp(iff(p1,p3), imp(iff(p0, p1), iff(p2, p3))))
  |- imp(iff(p1,p3), imp(iff(p0,p2), imp(iff(p0, p1), iff(p2, p3))))
} = {
  com12i(iff(p1,p3), iff(p0,p2), imp(iff(p0,p1),iff(p2,p3)))
  com12id(iff(p0,p2), iff(p1,p3), iff(p0,p1), iff(p2,p3))
  rw3(iff(p0,p2), iff(p0,p1), imp(iff(p1,p3),iff(p2,p3)), iff(p2,p1))
  iff.trans.1(p2, p1, p3)
  iff.trans.2(p1, p0, p2)
}
```

```follow
thm iff.2iffii.2(prop p0, prop p1, prop p2, prop p3) {
  |- imp(iff(p0, p1), iff(p2, p3))
  -| iff(p0,p2)
  -| iff(p1,p3)
} = {
  mp(imp(iff(p0,p1),iff(p2,p3)), iff(p1,p3))
  mp(imp(iff(p1,p3),imp(iff(p0,p1),iff(p2,p3))), iff(p0,p2))
  iff.2iff.2(p0, p1, p2, p3)
}
```

```follow
thm iff.2iffiid.2(prop p0, prop p1, prop p2, prop p3, prop p4) {
  |- imp(p4, imp(iff(p0, p1), iff(p2, p3)))
  -| imp(p4, iff(p0,p2))
  -| imp(p4, iff(p1,p3))
} = {
  mpd(p4, imp(iff(p0,p1),iff(p2,p3)), iff(p1,p3))
  syl(p4, imp(iff(p1,p3),imp(iff(p0,p1),iff(p2,p3))), iff(p0,p2))
  iff.2iff.2(p0, p1, p2, p3)
}
```

```follow
thm iff.iffiff(prop p0, prop p1, prop p2, prop p3) {
  |- imp(iff(p0,p2), imp(iff(p1,p3), iff(iff(p0, p1), iff(p2, p3))))
  |- imp(iff(p1,p3), imp(iff(p0,p2), iff(iff(p0, p1), iff(p2, p3))))
} = {
  com12i(iff(p1,p3), iff(p0,p2), iff(iff(p0,p1),iff(p2,p3)))
  and.spliti(iff(p0,p2), iff(p1,p3), iff(iff(p0,p1),iff(p2,p3)))
  iff.introiid.1(and(iff(p0,p2),iff(p1,p3)), iff(p0,p1), iff(p2,p3))
  and.joini(iff(p0,p2), iff(p1,p3), imp(iff(p0,p1),iff(p2,p3)))
  iff.2iff.2(p0, p1, p2, p3)
  syl(and(iff(p0,p2),iff(p1,p3)), imp(iff(p2,p3),iff(p0,p1)), and(iff(p2,p0),iff(p3,p1)))
  and.2andii.1(iff(p0,p2), iff(p1,p3), iff(p2,p0), iff(p3,p1))
  iff.com(p0, p2)
  iff.com(p1, p3)
  and.joini(iff(p2,p0), iff(p3,p1), imp(iff(p2,p3),iff(p0,p1)))
  iff.2iff.2(p2, p3, p0, p1)
}
```

```follow
thm iff.iffiffi(prop p0, prop p1, prop p2, prop p3) {
  |- iff(iff(p0, p1), iff(p2, p3))
  -| iff(p0,p2)
  -| iff(p1,p3)
} = {
  mp(iff(iff(p0,p1),iff(p2,p3)), iff(p0,p2))
  mp(imp(iff(p0,p2),iff(iff(p0,p1),iff(p2,p3))), iff(p1,p3))
  iff.iffiff(p0, p1, p2, p3)
}
```

```follow
thm iff.iffiffid(prop p0, prop p1, prop p2, prop p3, prop p4) {
  |- imp(p4, iff(iff(p0, p1), iff(p2, p3)))
  -| imp(p4, iff(p0,p2))
  -| imp(p4, iff(p1,p3))
} = {
  mpd(p4, iff(iff(p0,p1),iff(p2,p3)), iff(p0,p2))
  syl(p4, imp(iff(p0,p2),iff(iff(p0,p1),iff(p2,p3))), iff(p1,p3))
  iff.iffiff(p0, p1, p2, p3)
}
```

## 扩展前面的定义和公理  

```follow
thm iff.and.def(prop p0, prop p1) {
  |- iff(and(p0,p1),not(imp(p0,not(p1))))
  |- iff(not(imp(p0,not(p1))), and(p0,p1))
} = {
  iff.introii.1(and(p0,p1), not(imp(p0,not(p1))))
  iff.introii.1(not(imp(p0,not(p1))), and(p0,p1))
  and.def.1(p0, p1)
}
```

```follow
thm iff.or.def(prop p0, prop p1) {
  |- iff(or(p0,p1), imp(not(p0),p1))
  |- iff(imp(not(p0),p1), or(p0,p1))
} = {
  iff.introii.1(or(p0,p1), imp(not(p0),p1))
  iff.introii.1(imp(not(p0),p1), or(p0,p1))
  or.def.1(p0, p1)
}
```

```follow
thm iff.and.com(prop p0, prop p1) {
  |- iff(and(p0, p1), and(p1, p0))
  |- imp(and(p0, p1), and(p1, p0))
} = {
  iff.introii.1(and(p0,p1), and(p1,p0))
  and.com(p0, p1)
  and.com(p1, p0)
}
```

```follow
thm iff.and.syl(prop p0, prop p1, prop p2, prop p3, prop p4) {
  |- imp(and(p0,p1), iff(p2,p3))
  -| imp(p0,iff(p2,p4))
  -| imp(p1,iff(p4,p3))
} = {
  iff.syld(and(p0,p1), p2, p3, p4)
  syl(and(p0,p1), iff(p2,p4), p0)
  and.left(p0, p1)
  syl(and(p0,p1), iff(p4,p3), p1)
  and.right(p0, p1)
}
```

```follow
thm iff.or.com(prop p0, prop p1) {
  |- iff(or(p0, p1), or(p1, p0))
  |- imp(or(p0, p1), or(p1, p0))
} = {
  iff.introii.1(or(p0,p1), or(p1,p0))
  or.com(p0, p1)
  or.com(p1, p0)
}
```

```follow
thm iff.def.iff(prop p0, prop p1) {
  |- iff(iff(p0,p1),and(imp(p0,p1),imp(p1,p0)))
  |- iff(and(imp(p0,p1),imp(p1,p0)),iff(p0,p1))
} = {
  iff.introii.1(iff(p0,p1), and(imp(p0,p1),imp(p1,p0)))
  iff.introii.1(and(imp(p0,p1),imp(p1,p0)), iff(p0,p1))
  iff.def(p0, p1)
}
```

```follow
thm iff.notnot(prop p0) {
  |- iff(p0, not(not(p0)))
  |- iff(not(not(p0)),p0)
  |- imp(p0, not(not(p0)))
  |- imp(not(not(p0)),p0)
} = {
  iff.introii.1(p0, not(not(p0)))
  iff.introii.1(not(not(p0)), p0)
  notnot.1(p0)
  notnot.2(p0)
}
```

```follow
thm iff.con(prop p0, prop p1) {
  // 第一组
  |- iff(imp(p0, not(p1)), imp(p1, not(p0)))
  |- iff(imp(not(p0), p1), imp(not(p1), p0))
  |- iff(imp(p0, p1), imp(not(p1), not(p0)))
  |- iff(imp(not(p0), not(p1)), imp(p1, p0))

  // 第二组
  |- imp(iff(p0, not(p1)), iff(p1, not(p0)))
  |- imp(iff(not(p0), p1), iff(not(p1), p0))
  |- imp(iff(p0, p1), iff(not(p1), not(p0)))
  |- imp(iff(not(p0), not(p1)), iff(p1, p0))

  // 第三组
  |- imp(iff(p0, not(p1)), iff(not(p0), p1))
  |- imp(iff(not(p0), p1), iff(p0, not(p1)))
  |- imp(iff(p0, p1), iff(not(p0), not(p1)))
  |- imp(iff(not(p0), not(p1)), iff(p0, p1))
} = {
  iff.introii.1(imp(p0,not(p1)), imp(p1,not(p0)))
  iff.introii.1(imp(not(p0),p1), imp(not(p1),p0))
  iff.introii.1(imp(p0,p1), imp(not(p1),not(p0)))
  iff.introii.1(imp(not(p0),not(p1)), imp(p1,p0))

  iff.comid(iff(p0,not(p1)), not(p0), p1)
  iff.comid(iff(not(p0),p1), p0, not(p1))
  iff.comid(iff(p0,p1), not(p0), not(p1))
  iff.comid(iff(not(p0),not(p1)), p0, p1)

  iff.2iffii.1(p0, not(p1), p1, not(p0))
  iff.2iffii.1(not(p0), p1, not(p1), p0)
  iff.2iffii.1(p0, p1, not(p1), not(p0))
  iff.2iffii.1(not(p0), not(p1), p1, p0)

  con.1(p1, p0)
  con.1(p0, p1)
  con.2(p1, p0)
  con.2(p0, p1)
  con.3(p1, p0)
  con.3(p0, p1)
  con.4(p1, p0)
  con.4(p0, p1)
}
```

```follow
thm iff.coni.1(prop p0, prop p1) {
  |- iff(not(p0), p1)
  -| iff(not(p1), p0)
} = {
  mp(iff(not(p0),p1), iff(not(p1),p0))
  iff.con(p1, p0)
}
```

```follow
thm iff.coni.2(prop p0, prop p1) {
  |- iff(p0, not(p1))
  -| iff(p1, not(p0))
} = {
  mp(iff(p0,not(p1)), iff(p1,not(p0)))
  iff.con(p1, p0)
}
```

```follow
thm iff.coni.3(prop p0, prop p1) {
  |- iff(p0, p1)
  -| iff(not(p1), not(p0))
} = {
  mp(iff(p0,p1), iff(not(p1),not(p0)))
  iff.con(p1, p0)
}
```

```follow
thm iff.coni.4(prop p0, prop p1) {
  |- iff(not(p0), not(p1))
  -| iff(p1, p0)
} = {
  mp(iff(not(p0),not(p1)), iff(p1,p0))
  iff.con(p1, p0)
}
```

```follow
thm iff.conid.1(prop p0, prop p1, prop p2) {
  |- imp(p0, iff(not(p1), p2))
  -| imp(p0, iff(not(p2), p1))
} = {
  syl(p0, iff(not(p1),p2), iff(not(p2),p1))
  iff.con(p2, p1)
}
```

```follow
thm iff.conid.2(prop p0, prop p1, prop p2) {
  |- imp(p0, iff(p1, not(p2)))
  -| imp(p0, iff(p2, not(p1)))
} = {
  syl(p0, iff(p1,not(p2)), iff(p2,not(p1)))
  iff.con(p2, p1)
}
```

```follow
thm iff.conid.3(prop p0, prop p1, prop p2) {
  |- imp(p0, iff(p1, p2))
  -| imp(p0, iff(not(p2), not(p1)))
} = {
  syl(p0, iff(p1,p2), iff(not(p2),not(p1)))
  iff.con(p2, p1)
}
```

```follow
thm iff.conid.4(prop p0, prop p1, prop p2) {
  |- imp(p0, iff(not(p1), not(p2)))
  -| imp(p0, iff(p2, p1))
} = {
  syl(p0, iff(not(p1),not(p2)), iff(p2,p1))
  iff.con(p2, p1)
}
```

```follow
thm iff.mp.1(prop p0, prop p1, prop p2) {
  |- iff(p0, p1)
  -| iff(p0, imp(p2, p1))
  -| p2
} = {
  iff.syl(p0, p1, imp(p2,p1))
  iff.introii.1(imp(p2,p1), p1)
  a1(p1, p2)
  mp(imp(imp(p2,p1),p1), p2)
  iidd(p2, p1)
}
```

```follow
thm iff.mp.and(prop p0, prop p1, prop p2) {
  |- iff(p0, p1)
  -| iff(p0, and(p2, p1))
  -| p2
} = {
  iff.syl(p0, p1, and(p2,p1))
  iff.introii.1(and(p2,p1), p1)
  and.right(p2, p1)
  mp(imp(p1,and(p2,p1)), p2)
  and.intro(p2, p1)
}
```

```follow
thm iff.mp.2(prop p0, prop p1, prop p2) {
  |- iff(p0, imp(p2, p1))
  |- iff(imp(p2, p1), p0)
  -| iff(p0, p1)
  -| p2
} = {
  iff.comi(imp(p2,p1), p0)
  iff.syl(p0, imp(p2,p1), p1)
  iff.introii.1(p1, imp(p2,p1))
  a1(p1, p2)
  mp(imp(imp(p2,p1),p1), p2)
  iidd(p2, p1)
}
```

```follow
thm iff.mp.3(prop p0, prop p1, prop p2) {
  |- iff(p1, imp(p2, p0))
  |- iff(imp(p2, p0), p1)
  -| iff(p0, p1)
  -| p2
} = {
  iff.comi(imp(p2,p0), p1)
  iff.mp.2(p1, p0, p2)
  iff.comi(p1, p0)
}
```

## 复合定理 `and.iffand` 

```follow
thm and.iffand.1(prop p0, prop p1, prop p2, prop p3) {
  |- imp(iff(p0,p1), imp(iff(p2,p3), iff(and(p0,p2), and(p1,p3))))
  |- imp(iff(p2,p3), imp(iff(p0,p1), iff(and(p0,p2), and(p1,p3))))
  |- imp(and(iff(p0,p1), iff(p2,p3)), iff(and(p0,p2), and(p1,p3)))
  |- imp(and(iff(p2,p3), iff(p0,p1)), iff(and(p0,p2), and(p1,p3)))
} = {
  and.joini(iff(p2,p3), iff(p0,p1), iff(and(p0,p2),and(p1,p3)))
  com12i(iff(p2,p3), iff(p0,p1), iff(and(p0,p2),and(p1,p3)))
  and.spliti(iff(p0,p1), iff(p2,p3), iff(and(p0,p2),and(p1,p3)))
  iff.introiid.1(and(iff(p0,p1),iff(p2,p3)), and(p0,p2), and(p1,p3))
  syl(and(iff(p0,p1),iff(p2,p3)), imp(and(p0,p2),and(p1,p3)), and(imp(p0,p1),imp(p2,p3)))
  and.joini(imp(p0,p1), imp(p2,p3), imp(and(p0,p2),and(p1,p3)))
  and.2and.1(p0, p1, p2, p3)
  and.2andii.1(iff(p0,p1), iff(p2,p3), imp(p0,p1), imp(p2,p3))
  iff.left(p0, p1)
  iff.left(p2, p3)
  syl(and(iff(p0,p1),iff(p2,p3)), imp(and(p1,p3),and(p0,p2)), and(imp(p1,p0),imp(p3,p2)))
  and.joini(imp(p1,p0), imp(p3,p2), imp(and(p1,p3),and(p0,p2)))
  and.2and.1(p1, p0, p3, p2)
  and.2andii.1(iff(p0,p1), iff(p2,p3), imp(p1,p0), imp(p3,p2))
  iff.right(p0, p1)
  iff.right(p2, p3)
}
```

```follow
thm and.iffandii.1(prop p0, prop p1, prop p2, prop p3) {
  |- iff(and(p0,p2), and(p1,p3))
  -| iff(p0, p1)
  -| iff(p2, p3)
} = {
  mp(iff(and(p0,p2),and(p1,p3)), iff(p0,p1))
  mp(imp(iff(p0,p1),iff(and(p0,p2),and(p1,p3))), iff(p2,p3))
  and.iffand.1(p0, p1, p2, p3)
}
```

```follow
thm and.iffandiid.1(prop p0, prop p1, prop p2, prop p3, prop p4) {
  |- imp(p0, iff(and(p1,p3), and(p2,p4)))
  -| imp(p0, iff(p1, p2))
  -| imp(p0, iff(p3, p4))
} = {
  mpd(p0, iff(and(p1,p3),and(p2,p4)), iff(p1,p2))
  syl(p0, imp(iff(p1,p2),iff(and(p1,p3),and(p2,p4))), iff(p3,p4))
  and.iffand.1(p1, p2, p3, p4)
}
```

```follow
thm and.iffand.2(prop p0, prop p1, prop p2) {
  |- imp(imp(p0,iff(p1,p2)), iff(and(p0,p1),and(p0,p2)))
} = {
  iff.rw23(imp(p0,iff(p1,p2)), and(p0,p1), and(p0,p2), not(imp(p0,not(p1))), not(imp(p0,not(p2))))
  iff.and.def(p0, p1)
  iff.and.def(p0, p2)
  syl(imp(p0,iff(p1,p2)), iff(not(imp(p0,not(p1))),not(imp(p0,not(p2)))), iff(imp(p0,not(p2)),imp(p0,not(p1))))
  iff.con(imp(p0,not(p2)), imp(p0,not(p1)))
  syl(imp(p0,iff(p1,p2)), iff(imp(p0,not(p2)),imp(p0,not(p1))), imp(p0,iff(not(p2),not(p1))))
  imp.iffimp.1(p0, not(p2), not(p1))
  mp(imp(imp(p0,iff(p1,p2)),imp(p0,iff(not(p2),not(p1)))), imp(iff(p1,p2),iff(not(p2),not(p1))))
  trans.1(p0, iff(p1,p2), iff(not(p2),not(p1)))
  iff.con(p1, p2)
}
```

```follow
thm and.iffandi.2(prop p0, prop p1, prop p2) {
  |- iff(and(p0,p1),and(p0,p2))
  -| imp(p0,iff(p1,p2)) 
} = {
  mp(iff(and(p0,p1),and(p0,p2)), imp(p0,iff(p1,p2)))
  and.iffand.2(p0, p1, p2)
}
```

```follow
thm and.iffandid.2(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p0, iff(and(p1,p2),and(p1,p3)))
  -| imp(p0, imp(p1,iff(p2,p3)))
} = {
  syl(p0, iff(and(p1,p2),and(p1,p3)), imp(p1,iff(p2,p3)))
  and.iffand.2(p1, p2, p3)
}
```

```follow
thm and.iffand.3(prop p0, prop p1, prop p2) {
  |- imp(imp(p0,iff(p1,p2)), iff(and(p1,p0),and(p2,p0)))
} = {
  iff.rw23(imp(p0,iff(p1,p2)), and(p1,p0), and(p2,p0), and(p0,p1), and(p0,p2))
  iff.and.com(p1, p0)
  iff.and.com(p2, p0)
  and.iffand.2(p0, p1, p2)
}
```

```follow
thm and.iffandi.3(prop p0, prop p1, prop p2) {
  |- iff(and(p1,p0),and(p2,p0))
  -| imp(p0,iff(p1,p2)) 
} = {
  mp(iff(and(p1,p0),and(p2,p0)), imp(p0,iff(p1,p2)))
  and.iffand.3(p0, p1, p2)
}
```

```follow
thm and.iffandid.3(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p0, iff(and(p2,p1),and(p3,p1)))
  -| imp(p0, imp(p1,iff(p2,p3)))
} = {
  syl(p0, iff(and(p2,p1),and(p3,p1)), imp(p1,iff(p2,p3)))
  and.iffand.3(p1, p2, p3)
}
```

## 复合定理 `and.iff`

```follow
thm and.iff.1(prop p0, prop p1) {
  |- imp(p0, iff(and(p0,p1),p1))
  |- imp(p0, iff(p1, and(p0,p1)))
} = {
  iff.comid(p0, p1, and(p0,p1))
  iff.introiid.1(p0, and(p0,p1), p1)
  a1i(p0, imp(and(p0,p1),p1))
  and.right(p0, p1)
  and.intro(p0, p1)
}
```

```follow
thm and.iffi.1(prop p0, prop p1) {
  |- iff(and(p0,p1),p1)
  |- iff(p1, and(p0,p1))
  -| p0
} = {
  mp(iff(and(p0,p1),p1), p0)
  mp(iff(p1,and(p0,p1)), p0)
  and.iff.1(p0, p1)
}
```

```follow
thm and.iffid.1(prop p0, prop p1, prop p2) {
  |- imp(p2, iff(and(p0,p1),p1))
  |- imp(p2, iff(p1, and(p0,p1)))
  -| imp(p2, p0)
} = {
  syl(p2, iff(and(p0,p1),p1), p0)
  syl(p2, iff(p1,and(p0,p1)), p0)
  and.iff.1(p0, p1)
}
```

```follow
thm and.iff.2(prop p0, prop p1) {
  |- imp(p0, iff(and(p1,p0),p1))
  |- imp(p0, iff(p1, and(p1,p0)))
} = {
  iff.comid(p0, p1, and(p1,p0))
  iff.introiid.1(p0, and(p1,p0), p1)
  a1i(p0, imp(and(p1,p0),p1))
  and.left(p1, p0)
  and.intro(p1, p0)
}
```

```follow
thm and.iffi.2(prop p0, prop p1) {
  |- iff(and(p1,p0),p1)
  |- iff(p1, and(p1,p0))
  -| p0
} = {
  mp(iff(and(p1,p0),p1), p0)
  mp(iff(p1,and(p1,p0)), p0)
  and.iff.2(p0, p1)
}
```

```follow
thm and.iffid.2(prop p0, prop p1, prop p2) {
  |- imp(p2, iff(and(p1,p0),p1))
  |- imp(p2, iff(p1, and(p1,p0)))
  -| imp(p2, p0)
} = {
  syl(p2, iff(and(p1,p0),p1), p0)
  syl(p2, iff(p1,and(p1,p0)), p0)
  and.iff.2(p0, p1)
}
```

## 复合定理 `or.iffor` 

```follow
thm or.iffor(prop p0, prop p1, prop p2, prop p3) {
  |- imp(iff(p0,p1),imp(iff(p2,p3),iff(or(p0,p2),or(p1,p3))))
  |- imp(iff(p2,p3),imp(iff(p0,p1),iff(or(p0,p2),or(p1,p3))))
  |- imp(and(iff(p0,p1),iff(p2,p3)),iff(or(p0,p2),or(p1,p3)))
  |- imp(and(iff(p2,p3),iff(p0,p1)),iff(or(p0,p2),or(p1,p3)))
} = {
  and.joini(iff(p0,p1), iff(p2,p3), iff(or(p0,p2),or(p1,p3)))
  and.joini(iff(p2,p3), iff(p0,p1), iff(or(p0,p2),or(p1,p3)))
  com12i(iff(p2,p3), iff(p0,p1), iff(or(p0,p2),or(p1,p3)))
  and.spliti(iff(p0,p1), iff(p2,p3), iff(or(p0,p2),or(p1,p3)))
  iff.rw23(and(iff(p0,p1),iff(p2,p3)), or(p0,p2), or(p1,p3), imp(not(p0),p2), imp(not(p1),p3))
  iff.or.def(p0, p2)
  iff.or.def(p1, p3)
  and.joini(iff(p0,p1), iff(p2,p3), iff(imp(not(p0),p2),imp(not(p1),p3)))
  syl(iff(p0,p1), imp(iff(p2,p3),iff(imp(not(p0),p2),imp(not(p1),p3))), iff(not(p0),not(p1)))
  imp.iffimp.3(not(p0), not(p1), p2, p3)
  iff.con(p0, p1)
}
```

```follow
thm or.ifforii(prop p0, prop p1, prop p2, prop p3) {
  |- iff(or(p0,p2),or(p1,p3))
  -| iff(p0, p1)
  -| iff(p2, p3)
} = {
  mp(iff(or(p0,p2),or(p1,p3)), iff(p0,p1))
  mp(imp(iff(p0,p1),iff(or(p0,p2),or(p1,p3))), iff(p2,p3))
  or.iffor(p0, p1, p2, p3)
}
```

```follow
thm or.ifforiid(prop p0, prop p1, prop p2, prop p3, prop p4) {
  |- imp(p0, iff(or(p1,p3),or(p2,p4)))
  -| imp(p0, iff(p1, p2))
  -| imp(p0, iff(p3, p4))
} = {
  mpd(p0, iff(or(p1,p3),or(p2,p4)), iff(p1,p2))
  syl(p0, imp(iff(p1,p2),iff(or(p1,p3),or(p2,p4))), iff(p3,p4))
  or.iffor(p1, p2, p3, p4)
}
```

## 复合定理 `not.or`

```follow
thm not.or.1(prop p0, prop p1) {
  |- iff(not(or(p0, p1)), and(not(p0),not(p1)))
  |- iff(and(not(p0),not(p1)), not(or(p0, p1)))
  |- imp(not(or(p0, p1)), and(not(p0),not(p1)))
  |- imp(and(not(p0),not(p1)), not(or(p0, p1)))
} = {
  iff.comi(and(not(p0),not(p1)), not(or(p0,p1)))
  iff.lefti(not(or(p0,p1)), and(not(p0),not(p1)))
  iff.righti(and(not(p0),not(p1)), not(or(p0,p1)))
  iff.syl(not(or(p0,p1)), and(not(p0),not(p1)), not(imp(not(p0),not(not(p1)))))
  iff.and.def(not(p0), not(p1))
  mp(iff(not(or(p0,p1)),not(imp(not(p0),not(not(p1))))), iff(imp(not(p0),not(not(p1))),or(p0,p1)))
  iff.con(imp(not(p0),not(not(p1))), or(p0,p1))
  iff.syl(imp(not(p0),not(not(p1))), or(p0,p1), imp(not(p0),p1))
  iff.or.def(p0, p1)
  mp(iff(imp(not(p0),not(not(p1))),imp(not(p0),p1)), imp(not(p0),iff(not(not(p1)),p1)))
  imp.iffimp.1(not(p0), not(not(p1)), p1)
  a1i(not(p0), iff(not(not(p1)),p1))
  iff.notnot(p1)
}
```

```follow
thm not.or.2(prop p0, prop p1) {
  |- iff(not(or(not(p0),p1)), and(p0,not(p1)))
  |- iff(and(p0,not(p1)), not(or(not(p0),p1)))
  |- imp(not(or(not(p0),p1)), and(p0,not(p1)))
  |- imp(and(p0,not(p1)), not(or(not(p0),p1)))
} = {
  iff.comi(and(p0,not(p1)), not(or(not(p0),p1)))
  iff.lefti(not(or(not(p0),p1)), and(p0,not(p1)))
  iff.righti(and(p0,not(p1)), not(or(not(p0),p1)))

  iff.syl(not(or(not(p0),p1)), and(p0,not(p1)), and(not(not(p0)),not(p1)))
  not.or.1(not(p0), p1)
  and.iffandii.1(not(not(p0)), p0, not(p1), not(p1))
  iff.notnot(p0)
  iff.id(not(p1))
}
```

```follow
thm not.or.3(prop p0, prop p1) {
  |- iff(not(or(p0,not(p1))), and(not(p0),p1))
  |- iff(and(not(p0),p1), not(or(p0,not(p1))))
  |- imp(not(or(p0,not(p1))), and(not(p0),p1))
  |- imp(and(not(p0),p1), not(or(p0,not(p1))))
} = {
  iff.comi(and(not(p0),p1), not(or(p0,not(p1))))
  iff.lefti(not(or(p0,not(p1))), and(not(p0),p1))
  iff.righti(and(not(p0),p1), not(or(p0,not(p1))))
  iff.syl(not(or(p0,not(p1))), and(not(p0),p1), and(not(p0),not(not(p1))))
  not.or.1(p0, not(p1))
  and.iffandii.1(not(p0), not(p0), not(not(p1)), p1)
  iff.id(not(p0))
  iff.notnot(p1)
}
```

```follow
thm not.or.4(prop p0, prop p1) {
  |- iff(not(or(not(p0),not(p1))), and(p0,p1))
  |- iff(and(p0,p1), not(or(not(p0),not(p1))))
  |- imp(not(or(not(p0),not(p1))), and(p0,p1))
  |- imp(and(p0,p1), not(or(not(p0),not(p1))))
} = {
  iff.comi(and(p0,p1), not(or(not(p0),not(p1))))
  iff.lefti(not(or(not(p0),not(p1))), and(p0,p1))
  iff.righti(and(p0,p1), not(or(not(p0),not(p1))))
  iff.syl(not(or(not(p0),not(p1))), and(p0,p1), and(p0,not(not(p1))))
  not.or.2(p0, not(p1))
  and.iffandii.1(p0, p0, not(not(p1)), p1)
  iff.id(p0)
  iff.notnot(p1)
}
```

## 复合定理 `not.and` 

```follow
thm not.and.1(prop p0, prop p1) {
  |- iff(not(and(p0,p1)), or(not(p0),not(p1)))
  |- iff(or(not(p0),not(p1)), not(and(p0,p1)))
  |- imp(not(and(p0,p1)), or(not(p0),not(p1)))
  |- imp(or(not(p0),not(p1)), not(and(p0,p1)))
} = {
  iff.comi(or(not(p0),not(p1)), not(and(p0,p1)))
  iff.lefti(not(and(p0,p1)), or(not(p0),not(p1)))
  iff.righti(or(not(p0),not(p1)), not(and(p0,p1)))
  mp(iff(not(and(p0,p1)),or(not(p0),not(p1))), iff(not(or(not(p0),not(p1))),and(p0,p1)))
  iff.con(or(not(p0),not(p1)), and(p0,p1))
  not.or.4(p0, p1)
}
```

```follow
thm not.and.2(prop p0, prop p1) {
  |- iff(not(and(not(p0),p1)), or(p0,not(p1)))
  |- iff(or(p0,not(p1)), not(and(not(p0),p1)))
  |- imp(not(and(not(p0),p1)), or(p0,not(p1)))
  |- imp(or(p0,not(p1)), not(and(not(p0),p1)))
} = {
  iff.comi(or(p0,not(p1)), not(and(not(p0),p1)))
  iff.lefti(not(and(not(p0),p1)), or(p0,not(p1)))
  iff.righti(or(p0,not(p1)), not(and(not(p0),p1)))
  mp(iff(not(and(not(p0),p1)),or(p0,not(p1))), iff(not(or(p0,not(p1))),and(not(p0),p1)))
  iff.con(or(p0,not(p1)), and(not(p0),p1))
  not.or.3(p0, p1)
}
```

```follow
thm not.and.3(prop p0, prop p1) {
  |- iff(not(and(p0,not(p1))), or(not(p0),p1))
  |- iff(or(not(p0),p1), not(and(p0,not(p1))))
  |- imp(not(and(p0,not(p1))), or(not(p0),p1))
  |- imp(or(not(p0),p1), not(and(p0,not(p1))))
} = {
  iff.comi(or(not(p0),p1), not(and(p0,not(p1))))
  iff.lefti(not(and(p0,not(p1))), or(not(p0),p1))
  iff.righti(or(not(p0),p1), not(and(p0,not(p1))))
  mp(iff(not(and(p0,not(p1))),or(not(p0),p1)), iff(not(or(not(p0),p1)),and(p0,not(p1))))
  iff.con(or(not(p0),p1), and(p0,not(p1)))
  not.or.2(p0, p1)
}
```

```follow
thm not.and.4(prop p0, prop p1) {
  |- iff(not(and(not(p0), not(p1))), or(p0,p1))
  |- iff(or(p0,p1), not(and(not(p0), not(p1))))
  |- imp(not(and(not(p0), not(p1))), or(p0,p1))
  |- imp(or(p0,p1), not(and(not(p0), not(p1))))
} = {
  iff.comi(or(p0,p1), not(and(not(p0),not(p1))))
  iff.lefti(not(and(not(p0),not(p1))), or(p0,p1))
  iff.righti(or(p0,p1), not(and(not(p0),not(p1))))
  mp(iff(not(and(not(p0),not(p1))),or(p0,p1)), iff(not(or(p0,p1)),and(not(p0),not(p1))))
  iff.con(or(p0,p1), and(not(p0),not(p1)))
  not.or.1(p0, p1)
}
```