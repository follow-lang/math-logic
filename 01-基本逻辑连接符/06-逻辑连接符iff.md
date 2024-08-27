
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
}
```

```follow
thm iff.right(prop p0, prop p1) {
  |- imp(iff(p0,p1), imp(p1,p0))
} = {
}
```

```follow
thm iff.lefti(prop p0, prop p1) {
  |- imp(p0, p1)
  -| iff(p0, p1)
} = {
}
```

```follow
thm iff.leftid(prop p0, prop p1, prop p2) {
  |- imp(p0, imp(p1, p2))
  -| imp(p0, iff(p1, p2))
} = {
}
```

```follow
thm iff.righti(prop p0, prop p1) {
  |- imp(p0, p1)
  -| iff(p1, p0)
} = {
}
```

```follow
thm iff.rightid(prop p0, prop p1, prop p2) {
  |- imp(p0, imp(p1, p2))
  -| imp(p0, iff(p2, p1))
} = {
}
```

## 引入，`Introduction` 

```follow
thm iff.intro.1(prop p0, prop p1) {
  |- imp(imp(p0,p1),imp(imp(p1,p0),iff(p0,p1)))
  |- imp(imp(p1,p0),imp(imp(p0,p1),iff(p0,p1)))
} = {
}
```

```follow
thm iff.intro.2(prop p0, prop p1) {
  |- imp(p0, imp(p1, iff(p0, p1)))
  |- imp(p1, imp(p0, iff(p0, p1)))
  |- imp(and(p0,p1), iff(p0, p1))
  |- imp(and(p1,p0), iff(p0, p1))
} = {
}
```

```follow
thm iff.intro.3(prop p0, prop p1) {
  |- imp(not(p0), imp(not(p1), iff(p0, p1)))
  |- imp(not(p1), imp(not(p0), iff(p0, p1)))
  |- imp(and(not(p0),not(p1)), iff(p0, p1))
  |- imp(and(not(p1),not(p0)), iff(p0, p1))
} = {
}
```

```follow
thm iff.introii.1(prop p0, prop p1) {
  |- iff(p0, p1)
  -| imp(p0, p1)
  -| imp(p1, p0)
} = {
}
```

```follow
thm iff.introiid.1(prop p0, prop p1, prop p2) {
  |- imp(p0, iff(p1, p2))
  -| imp(p0, imp(p1, p2))
  -| imp(p0, imp(p2, p1))
} = {
}
```

```follow
thm iff.introii.2(prop p0, prop p1) {
  |- iff(p0, p1)
  -| p0
  -| p1
} = {
}
```

```follow
thm iff.introiid.2(prop p0, prop p1, prop p2) {
  |- imp(p0, iff(p1, p2))
  -| imp(p0, p1)
  -| imp(p0, p2)
} = {
}
```

```follow
thm iff.introii.3(prop p0, prop p1) {
  |- iff(p0, p1)
  -| not(p0)
  -| not(p1)
} = {
}
```

```follow
thm iff.introiid.3(prop p0, prop p1, prop p2) {
  |- imp(p0, iff(p1, p2))
  -| imp(p0, not(p1))
  -| imp(p0, not(p2))
} = {
}
```

## 交换律

```follow
thm iff.com(prop p0, prop p1) {
  |- iff(iff(p0,p1), iff(p1,p0))
  |- imp(iff(p0,p1), iff(p1,p0))
} = {
}
```

```follow
thm iff.comi(prop p0, prop p1) {
  |- iff(p0, p1)
  -| iff(p1, p0)
} = {
}
```

```follow
thm iff.comid(prop p0, prop p1, prop p2) {
  |- imp(p0, iff(p1, p2))
  -| imp(p0, iff(p2, p1))
} = {
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
}
```

```follow
thm iff.iid.1(prop p0, prop p1) {
  |- imp(p0, p1)
  -| imp(p0, iff(p1, p0))
}= {
}
```

```follow
thm iff.iid.2(prop p0, prop p1) {
  |- imp(p0, p1)
  -| imp(p0, iff(p0, p1))
}= {
}
```

## 传递性 `Transition`

```follow
thm iff.trans.1(prop p0, prop p1, prop p2) {
  |- imp(iff(p0, p1), imp(iff(p1, p2), iff(p0, p2)))
} = {
}
```

```follow
thm iff.trans.2(prop p0, prop p1, prop p2) {
  |- imp(iff(p0, p1), imp(iff(p0, p2), iff(p1, p2)))
  |- imp(iff(p0, p1), imp(iff(p1, p2), iff(p2, p0)))
  |- imp(iff(p0, p1), imp(iff(p0, p2), iff(p2, p1)))
  |- imp(iff(p0, p1), imp(iff(p2, p1), iff(p0, p2)))
  |- imp(iff(p0, p1), imp(iff(p2, p0), iff(p1, p2)))
  |- imp(iff(p0, p1), imp(iff(p2, p1), iff(p2, p0)))
  |- imp(iff(p0, p1), imp(iff(p2, p0), iff(p2, p1)))
} = {
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
}
```

```follow
thm iff.syld(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p0, iff(p1, p2))
  -| imp(p0, iff(p1, p3))
  -| imp(p0, iff(p3, p2))
} = {
}
```

## 替换某一个命题, `rewrite`

```follow
thm iff.rw2(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p0, iff(p1, p2))
  -| imp(p0, iff(p3, p2))
  -| iff(p1, p3)
} = {
}
```

```follow
thm iff.rw3(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p0, iff(p1, p2))
  -| imp(p0, iff(p1, p3))
  -| iff(p2, p3)
} = {
}
```

```follow
thm iff.rw23(prop p0, prop p1, prop p2, prop p3, prop p4) {
  |- imp(p0, iff(p1, p2))
  -| imp(p0, iff(p3, p4))
  -| iff(p1, p3)
  -| iff(p2, p4)
} = {
}
```

## 复合定理 `imp.iffimp`

```follow
thm imp.iffimp.1(prop p0, prop p1, prop p2) {
  |- imp(imp(p0,iff(p1,p2)), iff(imp(p0,p1),imp(p0,p2)))
} = {
}
```

```follow
thm imp.iffimp.2(prop p0, prop p1, prop p2) {
  |- imp(imp(p0,iff(p2,p1)), iff(imp(p0,p1),imp(p0,p2)))
} = {
}
```

```follow
thm imp.iffimp.3(prop p0, prop p1, prop p2, prop p3) {
  |- imp(iff(p0,p1),imp(iff(p2,p3),iff(imp(p0,p2),imp(p1,p3))))
  |- imp(iff(p2,p3),imp(iff(p0,p1),iff(imp(p0,p2),imp(p1,p3))))
  |- imp(and(iff(p0,p1),iff(p2,p3)),iff(imp(p0,p2),imp(p1,p3)))
} = {
}
```

```follow
thm imp.iffimp.4(prop p0, prop p1, prop p2) {
  |- imp(iff(p1, p2), iff(imp(p0, p1), imp(p0, p2)))
} = {
}
```

```follow
thm imp.iffimp.5(prop p0, prop p1, prop p2) {
  |- imp(iff(p1, p2), iff(imp(p1, p0), imp(p2, p0)))
} = {
}
```

```follow
thm imp.iffimpi.1(prop p0, prop p1, prop p2) {
  |- iff(imp(p0,p1),imp(p0,p2))
  -| imp(p0,iff(p1,p2)) 
} = {
}
```

```follow
thm imp.iffimpi.2(prop p0, prop p1, prop p2) {
  |- iff(imp(p0,p1),imp(p0,p2))
  -| imp(p0, iff(p1, p2))
} = {
}
```

```follow
thm imp.iffimpi.3(prop p0, prop p1, prop p2, prop p3) {
  |- iff(imp(p0,p1),imp(p2,p3))
  -| iff(p0, p2)
  -| iff(p1, p3)
} = {
}
```

```follow
thm imp.iffimpd.3(prop p0, prop p1, prop p2, prop p3, prop p4) {
  |- imp(p0, iff(imp(p1,p2),imp(p3,p4)))
  -| imp(p0, iff(p1, p3))
  -| imp(p0, iff(p2, p4))
} = {
}
```


```follow
thm imp.iffimpi.4(prop p0, prop p1, prop p2, prop p3) {
  |- iff(imp(p0, p1), imp(p0, p2))
  -| iff(p1, p2)
} = {
}
```

```follow
thm imp.iffimpd.4(prop p0, prop p1, prop p2, prop p3, prop p4) {
  |- imp(p0, iff(imp(p1, p2), imp(p1, p3)))
  -| imp(p0, iff(p2, p3))
} = {
}
```

```follow
thm imp.iffimpi.5(prop p0, prop p1, prop p2) {
  |- iff(imp(p1, p0), imp(p2, p0))
  -| iff(p1, p2)
} = {
}
```

```follow
thm imp.iffimpd.5(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p0, iff(imp(p2, p1), imp(p3, p1)))
  -| imp(p0, iff(p2, p3))
} = {
}
```

## 复合定理 `iff.2iff`

```follow
thm iff.2iff(prop p0, prop p1, prop p2, prop p3) {
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
}
```

```follow
thm iff.2iffii(prop p0, prop p1, prop p2, prop p3) {
  |- imp(iff(p0, p1), iff(p2, p3))
  -| imp(imp(p0,p1),imp(p2,p3))
  -| imp(imp(p1,p0),imp(p3,p2))
} = {
}
```

```follow
thm iff.2iffiid(prop p0, prop p1, prop p2, prop p3, prop p4) {
  |- imp(p0, imp(iff(p1, p2), iff(p3, p4)))
  -| imp(p0, imp(imp(p1,p2),imp(p3,p4)))
  -| imp(p0, imp(imp(p2,p1),imp(p4,p3)))
} = {
}
```

## 扩展前面的定义和公理  

```follow
thm and.def.iff(prop p0, prop p1) {
  |- iff(and(p0,p1),not(imp(p0,not(p1))))
  |- iff(not(imp(p0,not(p1))), and(p0,p1))
} = {
}
```

```follow
thm or.def.iff(prop p0, prop p1) {
  |- iff(or(p0,p1), imp(not(p0),p1))
  |- iff(imp(not(p0),p1), or(p0,p1))
} = {
}
```

```follow
thm and.com.iff(prop p0, prop p1) {
  |- iff(and(p0, p1), and(p1, p0))
} = {
}
```

```follow
thm or.com.iff(prop p0, prop p1) {
  |- iff(or(p0, p1), or(p1, p0))
} = {
}
```

```follow
thm iff.def.iff(prop p0, prop p1) {
  |- iff(iff(p0,p1),and(imp(p0,p1),imp(p1,p0)))
  |- iff(and(imp(p0,p1),imp(p1,p0)),iff(p0,p1))
} = {
}
```

```follow
thm notnot.iff(prop p0) {
  |- iff(p0, not(not(p0)))
  |- iff(not(not(p0)),p0)
} = {
}
```

```follow
thm con.iff(prop p0, prop p1) {
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
}
```

```follow
thm mp.iff(prop p0, prop p1, prop p2) {
  |- iff(p0, p1)
  -| iff(p0, imp(p2, p1))
  -| p2
} = {
}
```

```follow
thm mp.iff.and(prop p0, prop p1, prop p2) {
  |- iff(p0, p1)
  -| iff(p0, and(p2, p1))
  -| p2
} = {
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
}
```

```follow
thm and.iffandii.1(prop p0, prop p1, prop p2, prop p3) {
  |- iff(and(p0,p2), and(p1,p3))
  -| iff(p0, p1)
  -| iff(p2, p3)
} = {
}
```

```follow
thm and.iffandiid.1(prop p0, prop p1, prop p2, prop p3, prop p4) {
  |- imp(p0, iff(and(p1,p3), and(p2,p4)))
  -| imp(p0, iff(p1, p2))
  -| imp(p0, iff(p3, p4))
} = {
}
```

```follow
thm and.iffand.2(prop p0, prop p1, prop p2) {
  |- imp(imp(p0,iff(p1,p2)), iff(and(p0,p1),and(p0,p2)))
} = {
}
```

```follow
thm and.iffandi.2(prop p0, prop p1, prop p2) {
  |- iff(and(p0,p1),and(p0,p2))
  -| imp(p0,iff(p1,p2)) 
} = {
}
```

```follow
thm and.iffandid.2(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p0, iff(and(p1,p2),and(p1,p3)))
  -| imp(p0, imp(p1,iff(p2,p3)))
} = {
}
```

```follow
thm and.iffand.3(prop p0, prop p1, prop p2) {
  |- imp(imp(p0,iff(p1,p2)), iff(and(p1,p0),and(p2,p0)))
} = {
}
```

```follow
thm and.iffandi.3(prop p0, prop p1, prop p2) {
  |- iff(and(p1,p0),and(p2,p0))
  -| imp(p0,iff(p1,p2)) 
} = {
}
```

```follow
thm and.iffandid.3(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p0, iff(and(p2,p1),and(p3,p1)))
  -| imp(p0, imp(p1,iff(p2,p3)))
} = {
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
}
```

```follow
thm or.ifforii(prop p0, prop p1, prop p2, prop p3) {
  |- iff(or(p0,p2),or(p1,p3))
  -| iff(p0, p1)
  -| iff(p2, p3)
} = {
}
```

```follow
thm or.ifforiid(prop p0, prop p1, prop p2, prop p3, prop p4) {
  |- imp(p0, iff(or(p1,p3),or(p2,p4)))
  -| imp(p0, iff(p1, p2))
  -| imp(p0, iff(p3, p4))
} = {
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
}
```

```follow
thm not.or.2(prop p0, prop p1) {
  |- iff(not(or(not(p0),p1)), and(p0,not(p1)))
  |- iff(and(p0,not(p1)), not(or(not(p0),p1)))
  |- imp(not(or(not(p0),p1)), and(p0,not(p1)))
  |- imp(and(p0,not(p1)), not(or(not(p0),p1)))
} = {
}
```

```follow
thm not.or.3(prop p0, prop p1) {
  |- iff(not(or(p0,not(p1))), and(not(p0),p1))
  |- iff(and(not(p0),p1), not(or(p0,not(p1))))
  |- imp(not(or(p0,not(p1))), and(not(p0),p1))
  |- imp(and(not(p0),p1), not(or(p0,not(p1))))
} = {
}
```

```follow
thm not.or.4(prop p0, prop p1) {
  |- iff(not(or(not(p0),not(p1))), and(p0,p1))
  |- iff(and(p0,p1), not(or(not(p0),not(p1))))
  |- imp(not(or(not(p0),not(p1))), and(p0,p1))
  |- imp(and(p0,p1), not(or(not(p0),not(p1))))
} = {
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
}
```

```follow
thm not.and.2(prop p0, prop p1) {
  |- iff(not(and(not(p0),p1)), or(p0,not(p1)))
  |- iff(or(p0,not(p1)), not(and(not(p0),p1)))
  |- imp(not(and(not(p0),p1)), or(p0,not(p1)))
  |- imp(or(p0,not(p1)), not(and(not(p0),p1)))
} = {
}
```

```follow
thm not.and.3(prop p0, prop p1) {
  |- iff(not(and(p0,not(p1))), or(not(p0),p1))
  |- iff(or(not(p0),p1), not(and(p0,not(p1))))
  |- imp(not(and(p0,not(p1))), or(not(p0),p1))
  |- imp(or(not(p0),p1), not(and(p0,not(p1))))
} = {
}
```

```follow
thm not.and.4(prop p0, prop p1) {
  |- iff(not(and(not(p0), not(p1))), or(p0,p1))
  |- iff(or(p0,p1), not(and(not(p0), not(p1))))
  |- imp(not(and(not(p0), not(p1))), or(p0,p1))
  |- imp(or(p0,p1), not(and(not(p0), not(p1))))
} = {
}
```