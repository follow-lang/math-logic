# 逻辑连接符 `imp` 

## `Induction` 

`imp` 连接符号和 **目标命题与条件命题关系** 存在紧密的联系。

已知 `|- (p0->p1)`，那么一定能推出一个新的定理 `-| p0 |- p1`。

将 `p0` 和 `p1` 之间的联系从 `imp` 转化成 `-| |-` 之间的关系的过程，在一阶逻辑里叫做 `induction`。

```follow
thm theoremA(prop p0, prop p1) {
  |- imp(p0, p1)
} = {
  // 不同的定理对应不同的证明过程
}
thm induction_of_theoremA(prop p0, prop p1) {
  -| p0 |- p1
} = {
  // Induction定理
  mp(p1, p0)
  theoremA(p0, p1)
}
```
## `Deduction` 

如果，已知一个定理是 `-| p0 |- p1`，能否推出一个新的定理 `|- (p0->p1)` 呢？

```follow
thm theoremB(prop p0, prop p1) {
  -| p0 |- p1 
} = {
  // 不同的定理对应着不同的证明过程
}
thm deduction_of_theoremB(prop p0, prop p1) {
  |- imp(p0, p1)
} = {
  // Deduction定理：
  // 如果 theoremB 的证明过程只包含 `mp` `a1` 和 `a2` 这三个公理，
  // 或者由这三个公理推导出的定理，
  // 那么一定存在一个对应的证明过程，
  // 能够证明 deduction_of_theoremB 是正确的。
}
```

在一阶逻辑中存在一个这样的定理

> Deduction定理：
>  如果 theoremB 的证明过程只包含 `mp` `a1` 和 `a2` 这三个公理，或者由这三个公理推导出的定理,
>  那么一定存在一个对应的证明过程，能够证明 deduction_of_theoremB 是正确的。

这个定理的证明需要用到自然语言，超出了`Follow`语言的表达能力，在这个教程中涉及到的证明也不需要用到它。

后面我们也会遇到几次超出 `Follow` 语言表达能力的证明。这些证明暴露了 `Follow` 语言的表达边界。**暴露表达边界**也是 `Follow` 语言非常适合作为数理逻辑入门的原因。我们需要通过**自然语言**和**形式化证明语言**这两种客观事物的对比，才能逐渐形成的正确的抽象的**数理逻辑**。

因为很多时候，自然语言没有边界感，使用它的人们往往放飞自我，经常用感性的不符合数理逻辑的话，但往往也降低了表达的效率。而形式化证明语言都是有边界的，正是这个边界，将原来不可表达的，或者表达非常含糊的概念，要靠“师傅领进门，修行在个人”才能获取的概念，变得更容易获取了。

为了保持简单性，这个教程系列主要集中在 `Follow` 语言本身，以及 `Follow` 语言能够表达的一阶逻辑的命题们。它们是数理逻辑中的“房间里的大象”，是那头经常被忽略的“房间里的大象”。


## 开始证明 `imp` 相关的定理 

### 小试牛刀

```follow
// induction of a2
thm a2i(prop p0, prop p1, prop p2) {
  |- imp(imp(p0,p1),imp(p0,p2))
  -| imp(p0,imp(p1,p2))
} = {
}
```
```follow
// induction of induction of a2
thm a2ii(prop p0, prop p1, prop p2) {
  |- imp(p0,p1)
  -| imp(p0,p2)
  -| imp(p0,imp(p2,p1))
} = {
}
```

这个教程延续了 `Metamath` 里的 `setmm` 数据集的命名习惯。比如：
- 一个定理对应的 induction 版本的定理的名字是原名字后面加 `i`。
- 将一个定理的所有命题前面都添加一个 `imp` 操作，新形成的定理的名字是原名字后面添加 `d`，表示 `deduction`。

比如 `mp` 定理对应的 deduction 版本是 
```follow
// deduction of mp 
thm mpd(prop p0, prop p1, prop p2) {
  |- imp(p0, p1)
  -| imp(p0, p2)
  -| imp(p0,imp(p2,p1))
} = {
}
```

可以发现，公理 `mp` 的deduction版本就是公理 `a2` 的induction版本。
这不是一个巧合，公理 `a2` 就是这样逻辑学家人为构造出来的。

### `Identity`

```follow
// imp.identity
thm id(prop p0) {
  |- imp(p0, p0)
} = {
}
```

```follow
// id.deduction
thm idd(prop p0, prop p1) {
  |- imp(p0, imp(p1, p1))
} = {
}
```

```follow
// iid
thm iid(prop p0, prop p1) {
  |- imp(p0, p1)
  -| imp(p0, imp(p0, p1))
} = {
}
```

### 三段论 `syllogism` 

三段论是由古希腊哲学家亚里士多德提出的一种逻辑推演形式。它的英文名字 
`syllogism` 来自希腊语。
三段论是逻辑学中的最核心定理，在后面的证明过程中使用非常频繁。
所以这里给起了一个简称 `syl` 方便以后的使用。

```follow
thm syl(prop p0, prop p1, prop p2) {
  |- imp(p0, p1)
  -| imp(p0, p2)
  -| imp(p2, p1)
} = {
}
```

```follow
thm a1id(prop p0, prop p1, prop p2) {
  |- imp(p0, imp(p1, p2))
  -| imp(p0, p2)
} = {
}
```

```follow
thm a2id(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p0, imp(imp(p1, p2), imp(p1, p3)))
  -| imp(p0, imp(p1, imp(p2, p3)))
} = {
}
```

```follow
thm a2iid(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p0, imp(p1, p2))
  -| imp(p0, imp(p1, p3))
  -| imp(p0, imp(p1, imp(p3, p2)))
} = {
}
```

### 交换 `communication` 

```follow
thm com12i(prop p0, prop p1, prop p2) {
  |- imp(p0, imp(p1, p2))
  -| imp(p1, imp(p0, p2))
} = {
}
```

```follow
thm iidd(prop p0, prop p1) {
  |- imp(p0,imp(imp(p0,p1),p1))
} = {
}
```

```follow
thm com12(prop p0, prop p1, prop p2) {
  |- imp(imp(p0,imp(p1,p2)), imp(p1,imp(p0,p2)))
} = {
}
```

```follow
thm com12id(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p0, imp(p1, imp(p2, p3)))
  -| imp(p0, imp(p2, imp(p1, p3)))
} = {
}
```

### `imp` 的传递性 —— 三段论的本质  

```follow
thm trans.1(prop p0, prop p1, prop p2) {
  |- imp(imp(p1,p2),imp(imp(p0,p1),imp(p0,p2)))
} = {
}
```

```follow
thm trans.2(prop p0, prop p1, prop p2) {
  |- imp(imp(p0,p1),imp(imp(p1,p2),imp(p0,p2)))
} = {
}
```

这里有两个名字很像的定理 `trans.1` 和 `trans.2`，两个都是 `imp` 的传递性的体现。`Follow`插件能够提供一个功能，在输入`.`字符时，会搜索并尝试匹配所有相同开头的定理，所以，在后面的使用时，我们只需要输入 `trans.` 就可以了，插件会同时尝试用 `trans.1` 和 `trans.2` 两个定理去证明当前需要证明的目标命题。相当于存在一个定理 `trans`，它有两个输出，一个是 `|- ((p1→p2)→((p0→p1)→(p0→p2)))`，另一个是 `|- ((p0→p1)→((p1→p2)→(p0→p2)))`。

给类似的定理起相同开头的名字，这个技巧在后面会非常有用。

```follow
thm transi.1(prop p0, prop p1, prop p2) {
  |- imp(imp(p0,p1),imp(p0,p2))
  -| imp(p1,p2)
} = {
}
```

```follow
thm transi.2(prop p0, prop p1, prop p2) {
  |- imp(imp(p1,p2),imp(p0,p2))
  -| imp(p0, p1)
} = {
}
```

```follow
// syl.deduction
thm syld(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p0, imp(p1, p2))
  -| imp(p0, imp(p1, p3))
  -| imp(p0, imp(p3, p2))
} = {
}
```

### 替换某一个命题 `rewrite` 

这里介绍两个非常有用的定理。经常有一些 `p0->(p1->p2)` 形式的命题，在替换掉 `p1` 或者 `p2` 后会变得很好证明。

```follow
thm rw2(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p0, imp(p1, p2))
  -| imp(p0, imp(p3, p2))
  -| imp(p1, p3)
} = {
}
```

```follow
thm rw3(prop p0, prop p1, prop p2, prop p3) {
  |- imp(p0, imp(p1, p2))
  -| imp(p0, imp(p1, p3))
  -| imp(p3, p2)
} = {
}
```

```follow
thm rw23(prop p0, prop p1, prop p2, prop p3, prop p4) {
  |- imp(p0, imp(p1, p2))
  -| imp(p0, imp(p3, p4))
  -| imp(p1, p3)
  -| imp(p4, p2)
} = {
}
```

### `imp` 的传递性（续）—— 四连推理

```follow
thm trans4.1(prop p0, prop p1, prop p2, prop p3) {
  |- imp(imp(p0, p1), imp(imp(p1,p2), imp(imp(p2, p3), imp(p0,p3))))
} = {
}
```

在 `Follow` 语言中，公理或者定理可以有多个结论。 就好比电子芯片中的多输入多输出的元器件。
所有的输出都依赖同一组输入。

```follow
// trans4 的其他5种可能的形式 
thm trans4.2(prop p0, prop p1, prop p2, prop p3) {
  |- imp(imp(p0,p1), imp(imp(p2,p3), imp(imp(p1,p2), imp(p0,p3))))
  |- imp(imp(p1,p2), imp(imp(p0,p1), imp(imp(p2,p3), imp(p0,p3))))
  |- imp(imp(p1,p2), imp(imp(p2,p3), imp(imp(p0,p1), imp(p0,p3))))
  |- imp(imp(p2,p3), imp(imp(p0,p1), imp(imp(p1,p2), imp(p0,p3))))
  |- imp(imp(p2,p3), imp(imp(p1,p2), imp(imp(p0,p1), imp(p0,p3))))
} = {
}
```









