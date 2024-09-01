# 逻辑连接符 `and` 

**这也需要证明吗？** 是人们学习数理逻辑的时候，经常发出的吐槽。
很多逻辑定理我们都习以为常，这些概念是我们生活中逐渐积累产生的。
但是计算机没有生活，它什么都不知道。

我们可以把写Follow代码的过程，看成是给计算机上课。
教计算机上课有时候会很枯燥，因为我们经常会碰到 “这也需要证明吗” 的时候。
幸运的是，教它是简单的，因为它明确地告诉了我们它能理解的语言的规则。
只要在它的规则下书写的程序，它都能看懂。

计算机很笨，它不会怀疑自己遵循的规则。相比较而言，我们人类就太聪明了。我们在提问的时候，往往无法告诉回答者，答案需要遵循什么规则。
主要是因为我们太聪明了，我们往往会怀疑一切规则的合理性。当然也导致我们自己都搞不清楚自己相信了什么规则，是否正确。

我在网上看到一些表达：为什么要有公理呢？为什么要有证明规则呢？证明规则为什么这样设计？

有一个群人，他们从出生开始就待在一个房子里，从来没有出去过。他们大部分时间在研究这个屋子的门锁，因为他想出去。经常有人宣称打开了门锁，走出门一看，发现是另一个房间。就这样，房子里被发现的房间越来越多。没人知道这个房子有没有大门。可是这屋子里还有很多东西，有桌子，有椅子，有台灯，有冰箱，有空调，有电视机。当然还有一头叫做“逻辑”的大象，经常被人忽略。其实研究大象也挺有意思的，虽然不比电冰箱、电视机有用，但是挺有意思的。一不注意，大象就会打翻桌子，打碎台灯，所以了解它的习性还是挺重要的。

好的，我们今天来继续研究大象。

这一节课，我们介绍最常见的逻辑连接符`and`，表示“与”。很多人对`imp`连接符的真值表很疑惑，比如为什么`False->False`的值是`True` ，但是几乎没有人对`and`的真值表表示疑惑：只有两个输入都为真时，and的结果才为真。说明大家在脑海中产生了相同的“与”的抽象概念。但是在这个教程系列里，它的定义依赖 `imp` 和 `not`，也就是它的性质依赖 `imp` 和 `not` 的性质，所以在这一小节里我们会碰到很多**这也需要证明吗**的定理。

## 定义  

```follow
term prop and(prop p0, prop p1) { (p0 ∧ p1)}
```

```follow
axiom and.def.1(prop p0, prop p1) {
  |- imp(and(p0,p1),not(imp(p0,not(p1))))
  |- imp(not(imp(p0,not(p1))), and(p0,p1))
}
```

## 真值表 

| 名字 | 第一组值 | 第二组值 | 第三组值 | 第四组值 | 
| :---: | :---: | :---: | :---: | :---: |
| `p0` | 0 | 0 | 1 | 1 | 
| `p1` | 0 | 1 | 0 | 1 |
| `¬p1` | 1 | 0 | 1 | 0 | 
| `p0→(¬p1)` | 1 | 1 | 1 | 0 | 
| `¬(p0→(¬p1))` | 0 | 0 | 0 | 1 |

## 消去`and`命题, `Elimation` 

```follow
thm and.left(prop p0, prop p1) {
  |- imp(and(p0,p1), p0)
} = {
  syl(and(p0,p1), p0, not(imp(p0,not(p1))))
  and.def.1(p0, p1)
  coni.1(imp(p0,not(p1)), p0)
  cont.1(p0, not(p1))
}
```

```follow
thm and.lefti(prop p0, prop p1) {
  |- p0
  -| and(p0,p1)
} = {
  mp(p0, and(p0,p1))
  and.left(p0, p1)
}
```

```follow
thm and.leftid(prop p0, prop p1, prop p2) {
  |- imp(p0, p1)
  -| imp(p0, and(p1,p2))
} = {
  syl(p0, p1, and(p1,p2))
  and.left(p1, p2)
}
```

```follow
thm and.right(prop p0, prop p1) {
  |- imp(and(p0,p1), p1)
} = {
  syl(and(p0,p1), p1, not(imp(p0,not(p1))))
  and.def.1(p0, p1)
  coni.1(imp(p0,not(p1)), p1)
  a1(not(p1), p0)
}
```

```follow
thm and.righti(prop p0, prop p1) {
  |- p0
  -| and(p1, p0)
} = {
  mp(p0, and(p1,p0))
  and.right(p1, p0)
}
```

```follow
thm and.rightid(prop p0, prop p1, prop p2) {
  |- imp(p0, p1)
  -| imp(p0, and(p2, p1))
} = {
  syl(p0, p1, and(p2,p1))
  and.right(p2, p1)
}
```

## 引入 `Introduction` 

```follow
thm and.intro(prop p0, prop p1) {
  |- imp(p0, imp(p1, and(p0, p1)))
  |- imp(p1, imp(p0, and(p0, p1)))
} = {
  com12i(p1, p0, and(p0,p1))
  rw3(p0, p1, and(p0,p1), not(imp(p0,not(p1))))
  and.def.1(p0, p1)
  conid.2(p0, p1, imp(p0,not(p1)))
  iidd(p0, not(p1))
}
```

```follow
thm and.introii(prop p0, prop p1) {
  |- and(p0, p1)
  -| p0 
  -| p1
} = {
  mp(and(p0,p1), p0)
  mp(imp(p0,and(p0,p1)), p1)
  and.intro(p0, p1)
}
```

```follow
thm and.introiid(prop p0, prop p1, prop p2) {
  |- imp(p0, and(p1, p2))
  -| imp(p0, p1)
  -| imp(p0, p2)
} = {
  mpd(p0, and(p1,p2), p1)
  syl(p0, imp(p1,and(p1,p2)), p2)
  and.intro(p1, p2)
}
```

## 交换律

```follow
thm and.com(prop p0, prop p1) {
  |- imp(and(p0, p1), and(p1, p0))
} = {
  syl(and(p0,p1), and(p1,p0), not(imp(p0,not(p1))))
  and.def.1(p0, p1)
  syl(not(imp(p0,not(p1))), and(p1,p0), not(imp(p1,not(p0))))
  and.def.1(p1, p0)
  coni.4(imp(p0,not(p1)), imp(p1,not(p0)))
  con.2(p1, p0)
}
```

```follow
thm and.comi(prop p0, prop p1) {
  |- and(p0, p1)
  -| and(p1, p0)
} = {
  mp(and(p0,p1), and(p1,p0))
  and.com(p1, p0)
}
```

```follow
thm and.comid(prop p0, prop p1, prop p2) {
  |- imp(p0, and(p1, p2))
  -| imp(p0, and(p2, p1))
} = {
  syl(p0, and(p1,p2), and(p2,p1))
  and.com(p2, p1)
}
```

## Join To And Condition 合并成一个and条件

可以将两个imply的命题，合并成一个 `and` 的命题。

```follow
// 或者可以叫做 Importation Inference
thm and.join(prop p0, prop p1, prop p2) {
  |- imp(imp(p0,imp(p1,p2)), imp(and(p0,p1),p2))
} = {
  rw2(imp(p0,imp(p1,p2)), and(p0,p1), p2, not(imp(p0,not(p1))))
  and.def.1(p0, p1)
  conid.1(imp(p0,imp(p1,p2)), imp(p0,not(p1)), p2)
  rw2(imp(p0,imp(p1,p2)), not(p2), imp(p0,not(p1)), imp(imp(p1,p2),not(p1)))
  trans.2(p0, imp(p1,p2), not(p1))
  com12i(not(p2), imp(p1,p2), not(p1))
  con.4(p1, p2)
}
```

```follow
thm and.joini(prop p0, prop p1, prop p2) {
  |- imp(and(p0, p1), p2)
  -| imp(p0, imp(p1, p2))
} = {
  mp(imp(and(p0,p1),p2), imp(p0,imp(p1,p2)))
  and.join(p0, p1, p2)
}
```

```follow
thm and.joinid(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p0, imp(and(p1, p2), p3))
  -| imp(p0, imp(p1,imp(p2, p3)))
} = {
  syl(p0, imp(and(p1,p2),p3), imp(p1,imp(p2,p3)))
  and.join(p1, p2, p3)
}
```

## Split And Condition, 拆分and条件

```follow
thm and.split(prop p0, prop p1, prop p2) {
  |- imp(imp(and(p0,p1),p2), imp(p0,imp(p1,p2)))
} = {
  rw2(imp(and(p0,p1),p2), p0, imp(p1,p2), imp(p1,and(p0,p1)))
  trans.1(p1, and(p0,p1), p2)
  and.intro(p0, p1)
}
```

```follow
thm and.spliti(prop p0, prop p1, prop p2) {
  |- imp(p0,imp(p1,p2))
  -| imp(and(p0,p1),p2)
} = {
  mp(imp(p0,imp(p1,p2)), imp(and(p0,p1),p2))
  and.split(p0, p1, p2)
}
```

```follow
thm and.splitid(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p0, imp(p1,imp(p2, p3)))
  -| imp(p0, imp(and(p1, p2), p3))
} = {
  syl(p0, imp(p1,imp(p2,p3)), imp(and(p1,p2),p3))
  and.split(p1, p2, p3)
}
```

## 替换某一个命题, `rewrite`

```follow
thm and.rw2(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p0, and(p1, p2))
  -| imp(p0, and(p3, p2))
  -| imp(p3, p1)
} = {
  and.introiid(p0, p1, p2)
  syl(p0, p1, p3)
  and.leftid(p0, p3, p2)
  and.rightid(p0, p2, p3)
}
```

```follow
thm and.rw3(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p0, and(p1, p2))
  -| imp(p0, and(p1, p3))
  -| imp(p3, p2)
} = {
  and.introiid(p0, p1, p2)
  syl(p0, p2, p3)
  and.leftid(p0, p1, p3)
  and.rightid(p0, p3, p1)
}
```

```follow
thm and.rw23(prop p0, prop p1, prop p2, prop p3, prop p4) {
  |- imp(p0, and(p1, p2))
  -| imp(p0, and(p3, p4))
  -| imp(p3, p1)
  -| imp(p4, p2)
} = {
  and.rw2(p0, p1, p2, p3)
  and.rw3(p0, p3, p2, p4)
}
```

## 复合关系 `and.2and` 

```follow
thm and.2and.1(prop p0, prop p1, prop p2, prop p3) {
  |- imp(imp(p0,p1),imp(imp(p2,p3),imp(and(p0,p2),and(p1,p3))))
  |- imp(imp(p2,p3),imp(imp(p0,p1),imp(and(p0,p2),and(p1,p3))))
} = {
  com12i(imp(p2,p3), imp(p0,p1), imp(and(p0,p2),and(p1,p3)))
  and.spliti(imp(p0,p1), imp(p2,p3), imp(and(p0,p2),and(p1,p3)))
  rw23(and(imp(p0,p1),imp(p2,p3)), and(p0,p2), and(p1,p3), not(imp(p0,not(p2))), not(imp(p1,not(p3))))
  and.def.1(p0, p2)
  and.def.1(p1, p3)
  conid.4(and(imp(p0,p1),imp(p2,p3)), imp(p0,not(p2)), imp(p1,not(p3)))
  and.joini(imp(p0,p1), imp(p2,p3), imp(imp(p1,not(p3)),imp(p0,not(p2))))
  rw2(imp(p0,p1), imp(p2,p3), imp(imp(p1,not(p3)),imp(p0,not(p2))), imp(not(p3),not(p2)))
  trans4.2(p0, p1, not(p3), not(p2))
  con.4(p2, p3)
}
```

```follow
thm and.2andii.1(prop p0, prop p1, prop p2, prop p3) {
  |- imp(and(p0,p1),and(p2,p3))
  -| imp(p0,p2)
  -| imp(p1,p3)
} = {
  mp(imp(and(p0,p1),and(p2,p3)), imp(p0,p2))
  mp(imp(imp(p0,p2),imp(and(p0,p1),and(p2,p3))), imp(p1,p3))
  and.2and.1(p0, p2, p1, p3)
}
```

```follow
thm and.2andiid.1(prop p0, prop p1, prop p2, prop p3, prop p4) {
  |- imp(p0, imp(and(p1,p2),and(p3,p4)))
  -| imp(p0, imp(p1,p3))
  -| imp(p0, imp(p2,p4))
} = {
  mpd(p0, imp(and(p1,p2),and(p3,p4)), imp(p1,p3))
  syl(p0, imp(imp(p1,p3),imp(and(p1,p2),and(p3,p4))), imp(p2,p4))
  and.2and.1(p1, p3, p2, p4)
}
```

```follow
thm and.2and.2(prop p0, prop p1, prop p2) {
  |- imp(imp(p0,p1),imp(and(p0,p2),and(p1,p2)))
  |- imp(imp(p0,p1),imp(and(p2,p0),and(p2,p1)))
  |- imp(imp(p0,p1),imp(and(p0,p2),and(p2,p1)))
  |- imp(imp(p0,p1),imp(and(p2,p0),and(p1,p2)))
} = {
  rw3(imp(p0,p1), and(p0,p2), and(p2,p1), and(p1,p2))
  and.com(p1, p2)
  rw3(imp(p0,p1), and(p2,p0), and(p1,p2), and(p2,p1))
  and.com(p2, p1)
  mp(imp(imp(p0,p1),imp(and(p0,p2),and(p1,p2))), imp(p2,p2))
  and.2and.1(p0, p1, p2, p2)
  mp(imp(imp(p0,p1),imp(and(p2,p0),and(p2,p1))), imp(p2,p2))
  and.2and.1(p2, p2, p0, p1)
  id(p2)
}
```

```follow
thm and.2andi.2(prop p0, prop p1, prop p2) {
  |- imp(and(p0,p2),and(p1,p2))
  |- imp(and(p2,p0),and(p2,p1))
  |- imp(and(p0,p2),and(p2,p1))
  |- imp(and(p2,p0),and(p1,p2))
  -| imp(p0,p1)
} = {
  mp(imp(and(p0,p2),and(p2,p1)), imp(p0,p1))
  mp(imp(and(p2,p0),and(p1,p2)), imp(p0,p1))
  mp(imp(and(p0,p2),and(p1,p2)), imp(p0,p1))
  mp(imp(and(p2,p0),and(p2,p1)), imp(p0,p1))
  and.2and.2(p0, p1, p2)
}
```

```follow
thm and.2andid.2(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p3, imp(and(p0,p2),and(p1,p2)))
  |- imp(p3, imp(and(p2,p0),and(p2,p1)))
  |- imp(p3, imp(and(p0,p2),and(p2,p1)))
  |- imp(p3, imp(and(p2,p0),and(p1,p2)))
  -| imp(p3, imp(p0,p1))
} = {
  syl(p3, imp(and(p0,p2),and(p1,p2)), imp(p0,p1))
  syl(p3, imp(and(p2,p0),and(p2,p1)), imp(p0,p1))
  syl(p3, imp(and(p0,p2),and(p2,p1)), imp(p0,p1))
  syl(p3, imp(and(p2,p0),and(p1,p2)), imp(p0,p1))
  and.2and.2(p0, p1, p2)
}
```

```follow
thm and.2and.3(prop p0, prop p1, prop p2) {
  |- imp(imp(p0,imp(p1,p2)),imp(and(p0,p1),and(p0,p2)))
  |- imp(imp(p0,imp(p1,p2)),imp(and(p1,p0),and(p0,p2)))
  |- imp(imp(p0,imp(p1,p2)),imp(and(p0,p1),and(p2,p0)))
  |- imp(imp(p0,imp(p1,p2)),imp(and(p1,p0),and(p2,p0)))
} = {
  rw2(imp(p0,imp(p1,p2)), and(p1,p0), and(p2,p0), and(p0,p1))
  and.com(p1, p0)
  rw2(imp(p0,imp(p1,p2)), and(p1,p0), and(p0,p2), and(p0,p1))
  and.com(p1, p0)
  rw3(imp(p0,imp(p1,p2)), and(p0,p1), and(p2,p0), and(p0,p2))
  and.com(p0, p2)

  rw23(imp(p0,imp(p1,p2)), and(p0,p1), and(p0,p2), not(imp(p0,not(p1))), not(imp(p0,not(p2))))
  and.def.1(p0, p1)
  and.def.1(p0, p2)
  conid.4(imp(p0,imp(p1,p2)), imp(p0,not(p1)), imp(p0,not(p2)))
  a2id(imp(p0,imp(p1,p2)), p0, not(p2), not(p1))
  transi.1(p0, imp(p1,p2), imp(not(p2),not(p1)))
  con.4(p1, p2)
}
```

```follow
thm and.2andi.3(prop p0, prop p1, prop p2) {
  |- imp(and(p0,p1),and(p0,p2))
  |- imp(and(p1,p0),and(p0,p2))
  |- imp(and(p0,p1),and(p2,p0))
  |- imp(and(p1,p0),and(p2,p0))
  -| imp(p0,imp(p1,p2))
} = {
  mp(imp(and(p0,p1),and(p0,p2)), imp(p0,imp(p1,p2)))
  mp(imp(and(p1,p0),and(p0,p2)), imp(p0,imp(p1,p2)))
  mp(imp(and(p0,p1),and(p2,p0)), imp(p0,imp(p1,p2)))
  mp(imp(and(p1,p0),and(p2,p0)), imp(p0,imp(p1,p2)))
  and.2and.3(p0, p1, p2)
}
```

```follow
thm and.2andid.3(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p3, imp(and(p0,p1),and(p0,p2)))
  |- imp(p3, imp(and(p1,p0),and(p0,p2)))
  |- imp(p3, imp(and(p0,p1),and(p2,p0)))
  |- imp(p3, imp(and(p1,p0),and(p2,p0)))
  -| imp(p3, imp(p0,imp(p1,p2)))
} = {
  syl(p3, imp(and(p0,p1),and(p0,p2)), imp(p0,imp(p1,p2)))
  syl(p3, imp(and(p1,p0),and(p0,p2)), imp(p0,imp(p1,p2)))
  syl(p3, imp(and(p0,p1),and(p2,p0)), imp(p0,imp(p1,p2)))
  syl(p3, imp(and(p1,p0),and(p2,p0)), imp(p0,imp(p1,p2)))
  and.2and.3(p0, p1, p2)
}
```

```follow
thm and.rw.left(prop p0, prop p1, prop p2) {
  |- and(p0, p1)
  -| and(p2, p1)
  -| imp(p2, p0)
} = {
  mp(and(p0,p1), and(p2,p1))
  and.2andii.1(p2, p1, p0, p1)
  id(p1)
}
```

```follow
thm and.rw.right(prop p0, prop p1, prop p2) {
  |- and(p0, p1)
  -| and(p0, p2)
  -| imp(p2, p1)
} = {
  mp(and(p0,p1), and(p0,p2))
  and.2andii.1(p0, p2, p0, p1)
  id(p0)
}
```


```follow
thm and.syl(prop p0, prop p1, prop p2, prop p3, prop p4) {
  |- imp(and(p0,p1), imp(p2,p3))
  -| imp(p0,imp(p2,p4))
  -| imp(p1,imp(p4,p3))
} = {
  syld(and(p0,p1), p2, p3, p4)
  syl(and(p0,p1), imp(p2,p4), p0)
  and.left(p0, p1)
  syl(and(p0,p1), imp(p4,p3), p1)
  and.right(p0, p1)
}
```

```follow
thm and.2and.2andii(prop p0, prop p1, prop p2, prop p3, prop p4, prop p5) {
  |- imp(and(p0,p1),imp(and(p2,p3),and(p4,p5)))
  -| imp(p0,imp(p2,p4))
  -| imp(p1,imp(p3,p5))
} = {
  and.2andiid.1(and(p0,p1), p2, p3, p4, p5)
  syl(and(p0,p1), imp(p2,p4), p0)
  and.left(p0, p1)
  syl(and(p0,p1), imp(p3,p5), p1)
  and.right(p0, p1)
}
```

## 无矛盾律 Noncontradiction 

```follow
thm and.not(prop p0) {
  |- not(and(p0, not(p0)))
  |- not(and(not(p0), p0))
} = {
  mp(not(and(not(p0),p0)), not(and(p0,not(p0))))
  coni.4(and(p0,not(p0)), and(not(p0),p0))
  and.com(not(p0), p0)
  mp(not(and(p0,not(p0))), imp(p0,not(not(p0))))
  coni.2(imp(p0,not(not(p0))), and(p0,not(p0)))
  and.def.1(p0, not(p0))
  notnot.2(p0)
}
```

## `imp.trans4.3`

```follow
// trans4 的其他5种可能的形式 
thm trans4.3(prop p0, prop p1, prop p2, prop p3) {
  |- imp(and(imp(p0,p1), imp(p2,p3)), imp(imp(p1,p2), imp(p0,p3))))
  |- imp(and(imp(p1,p2), imp(p0,p1)), imp(imp(p2,p3), imp(p0,p3))))
  |- imp(and(imp(p1,p2), imp(p2,p3)), imp(imp(p0,p1), imp(p0,p3))))
  |- imp(and(imp(p2,p3), imp(p0,p1)), imp(imp(p1,p2), imp(p0,p3))))
  |- imp(and(imp(p2,p3), imp(p1,p2)), imp(imp(p0,p1), imp(p0,p3))))
} = {
  and.joini(imp(p0,p1), imp(p2,p3), imp(imp(p1,p2),imp(p0,p3)))
  and.joini(imp(p1,p2), imp(p0,p1), imp(imp(p2,p3),imp(p0,p3)))
  and.joini(imp(p1,p2), imp(p2,p3), imp(imp(p0,p1),imp(p0,p3)))
  and.joini(imp(p2,p3), imp(p0,p1), imp(imp(p1,p2),imp(p0,p3)))
  and.joini(imp(p2,p3), imp(p1,p2), imp(imp(p0,p1),imp(p0,p3)))
  trans4.2(p0, p1, p2, p3)
}
```

## 复合关系，`imp.andimp`

```follow
thm imp.andimp.1(prop p0, prop p1, prop p2, prop p3) {
  |- imp(and(not(p0), not(p2)), and(imp(p0, p1), imp(p2, p3)))
  |- imp(and(not(p2), not(p0)), and(imp(p0, p1), imp(p2, p3)))
} = {
  syl(and(not(p2),not(p0)), and(imp(p0,p1),imp(p2,p3)), and(not(p0),not(p2)))
  and.com(not(p2), not(p0))
  and.2andii.1(not(p0), not(p2), imp(p0,p1), imp(p2,p3))
  cont.1(p0, p1)
  cont.1(p2, p3)
}
```

```follow
thm imp.andimp.2(prop p0, prop p1, prop p2, prop p3) {
  |- imp(and(not(p0), p3), and(imp(p0, p1), imp(p2, p3)))
  |- imp(and(p3, not(p0)), and(imp(p0, p1), imp(p2, p3)))
} = {
  syl(and(p3,not(p0)), and(imp(p0,p1),imp(p2,p3)), and(not(p0),p3))
  and.com(p3, not(p0))
  and.2andii.1(not(p0), p3, imp(p0,p1), imp(p2,p3))
  cont.1(p0, p1)
  a1(p3, p2)
}
```

```follow
thm imp.andimp.3(prop p0, prop p1, prop p2, prop p3) {
  |- imp(and(p1, not(p2)), and(imp(p0, p1), imp(p2, p3)))
  |- imp(and(not(p2), p1), and(imp(p0, p1), imp(p2, p3)))
} = {
  syl(and(not(p2),p1), and(imp(p0,p1),imp(p2,p3)), and(p1,not(p2)))
  and.com(not(p2), p1)
  and.2andii.1(p1, not(p2), imp(p0,p1), imp(p2,p3))
  a1(p1, p0)
  cont.1(p2, p3)
}
```

```follow
thm imp.andimp.4(prop p0, prop p1, prop p2, prop p3) {
  |- imp(and(p1, p3), and(imp(p0, p1), imp(p2, p3)))
  |- imp(and(p3, p1), and(imp(p0, p1), imp(p2, p3)))
} = {
  syl(and(p3,p1), and(imp(p0,p1),imp(p2,p3)), and(p1,p3))
  and.com(p3, p1)
  and.2andii.1(p1, p3, imp(p0,p1), imp(p2,p3))
  a1(p1, p0)
  a1(p3, p2)
}
```
