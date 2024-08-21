
# 逻辑连接符 `and` 

**这也需要证明？** 是人们学习形式化证明中，经常发出的吐槽。我们可以尝试客观化主体，或者将计算机当成一个小孩，很多定理我们都习以为常，这是我们成长生活中逐渐积累产生的。但是计算机没有生活，它什么都不知道，所以我们需要把这些“这也需要证明”的定理教给他。

与连接符`and`是更常见的逻辑连接符。我了解到很多人对`imp`连接符的真值表很疑惑，比如为什么`False->False`的值是`True` ，但是对`and`的真值表很确定，两个输入都为真时，结果才为真。大家在脑海中产生了相同的`and`的抽象概念，并且对`and`的性质了如指掌。但是在这个系列里，它的定义依赖 `imp` 和 `not`。它的性质也依赖 `imp` 和 `not` 的性质。所以在这一小节里我们会碰到很多 **这也需要证明** 的定理。

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

## 消去 `Elimation` 

```follow
thm and.left(prop p0, prop p1) {
  |- imp(and(p0,p1), p0)
} = {
}
```

```follow
thm and.lefti(prop p0, prop p1) {
  |- p0
  -| and(p0,p1)
} = {
}
```

```follow
thm and.leftid(prop p0, prop p1, prop p2) {
  |- imp(p0, p1)
  -| imp(p0, and(p1,p2))
} = {
}
```

```follow
thm and.right(prop p0, prop p1) {
  |- imp(and(p0,p1), p1)
} = {
}
```

```follow
thm and.righti(prop p0, prop p1) {
  |- p0
  -| and(p1, p0)
} = {
}
```

```follow
thm and.rightid(prop p0, prop p1, prop p2) {
  |- imp(p0, p1)
  -| imp(p0, and(p2, p1))
} = {
}
```

## 引入 `Introduction` 

```follow
thm and.intro(prop p0, prop p1) {
  |- imp(p0, imp(p1, and(p0, p1)))
  |- imp(p1, imp(p0, and(p0, p1)))
} = {
}
```

```follow
thm and.introii(prop p0, prop p1) {
  |- and(p0, p1)
  -| p0 
  -| p1
} = {
}
```

```follow
thm and.introiid(prop p0, prop p1, prop p2) {
  |- imp(p0, and(p1, p2))
  -| imp(p0, p1)
  -| imp(p0, p2)
} = {
}
```

## 交换律

```follow
thm and.com(prop p0, prop p1) {
  |- imp(and(p0, p1), and(p1, p0))
} = {
}
```

```follow
thm and.comi(prop p0, prop p1) {
  |- and(p0, p1)
  -| and(p1, p0)
} = {
}
```

```follow
thm and.comid(prop p0, prop p1, prop p2) {
  |- imp(p0, and(p1, p2))
  -| imp(p0, and(p2, p1))
} = {
}
```

## Split And Condition 拆分and条件

如果一个命题的条件是 `and` 形式的，可以将条件拆分。

```follow
// 或者可以叫做 Importation Inference
thm and.split(prop p0, prop p1, prop p2) {
  |- imp(imp(p0,imp(p1,p2)), imp(and(p0,p1),p2))
} = {
}
```

```follow
thm and.spliti(prop p0, prop p1, prop p2) {
  |- imp(and(p0, p1), p2)
  -| imp(p0, imp(p1, p2))
} = {
}
```

```follow
thm and.splitid(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p0, imp(and(p1, p2), p3))
  -| imp(p0, imp(p1,imp(p2, p3)))
} = {
}
```

## Join Condition To And 将两个条件合并成一个and条件

```follow
thm and.join(prop p0, prop p1, prop p2) {
  |- imp(imp(and(p0,p1),p2), imp(p0,imp(p1,p2)))
} = {
}
```

```follow
thm and.joini(prop p0, prop p1, prop p2) {
  |- imp(p0,imp(p1,p2))
  -| imp(and(p0,p1),p2)
} = {
}
```

```follow
thm and.joinid(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p0, imp(p1,imp(p2, p3)))
  -| imp(p0, imp(and(p1, p2), p3))
} = {
}
```

## 替换某一个命题, `rewrite`

```follow
thm and.rw2(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p0, and(p1, p2))
  -| imp(p0, and(p3, p2))
  -| imp(p3, p1)
} = {
}
```

```follow
thm and.rw3(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p0, and(p1, p2))
  -| imp(p0, and(p1, p3))
  -| imp(p3, p2)
} = {
}
```

```follow
thm and.rw23(prop p0, prop p1, prop p2, prop p3, prop p4) {
  |- imp(p0, and(p1, p2))
  -| imp(p0, and(p3, p4))
  -| imp(p3, p1)
  -| imp(p4, p2)
} = {
}
```

## 复合关系 `and.2and` 

```follow
thm and.2and(prop p0, prop p1, prop p2, prop p3) {
  |- imp(imp(p0,p1),imp(imp(p2,p3),imp(and(p0,p2),and(p1,p3))))
  |- imp(imp(p2,p3),imp(imp(p0,p1),imp(and(p0,p2),and(p1,p3))))
  |- imp(and(imp(p0,p1),imp(p2,p3)),imp(and(p0,p2),and(p1,p3)))
  |- imp(and(imp(p2,p3),imp(p0,p1)),imp(and(p0,p2),and(p1,p3)))
} = {
}
```

```follow
thm and.2andii(prop p0, prop p1, prop p2, prop p3) {
  |- imp(and(p0,p1),and(p2,p3))
  -| imp(p0,p2)
  -| imp(p1,p3)
} = {
}
```

```follow
thm and.2andiid(prop p0, prop p1, prop p2, prop p3, prop p4) {
  |- imp(p0, imp(and(p1,p2),and(p3,p4)))
  -| imp(p0, imp(p1,p3))
  -| imp(p0, imp(p2,p4))
} = {
}
```

```follow
thm and.syl(prop p0, prop p1, prop p2, prop p3, prop p4) {
  |- imp(and(p0,p1), imp(p2,p3))
  -| imp(p0,imp(p2,p4))
  -| imp(p1,imp(p4,p3))
} = {
}
```

## 复合关系 `and.not` 

```follow
thm and.not(prop p0) {
  |- not(and(p0, not(p0)))
  |- not(and(not(p0), p0))
} = {
}
```