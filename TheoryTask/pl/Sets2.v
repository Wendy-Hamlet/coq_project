Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. Import SetsNotation.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

(** * 集合运算性质的证明 *)

(** ** 交集与并集性质的Coq证明 *)

(** 相应的，要证明两个集合相等，就只需要证明它们相互包含。在Coq中只需要_[apply]_下面引
    理来实现这个证明步骤。
   
        Sets_equiv_Sets_included:
          forall x y, x == y <-> x ⊆ y /\ y ⊆ x
      
    要证明某两个集合的交集包含第三个集合，或者证明某两个集合的交集被第三个集合包含，又
    可以采取以下方法。

        _[x ⊆ y ∩ z]_可以被规约为_[x ⊆ y]_与_[x ⊆ z]_; 

        _[x ∩ y ⊆ z]_可以被规约为_[x ⊆ z]_; 

        _[x ∩ y ⊆ z]_也可以被规约为_[y ⊆ z]_。 

    在Coq中，前一种证明可以通过_[apply]_下面引理实现。
   
        Sets_included_intersect:
          forall x y z, x ⊆ y -> x ⊆ z -> x ⊆ y ∩ z
      
    而后两种证明可以通过_[rewrite]_下面引理实现。
   
        Sets_intersect_included1:
          forall x y, x ∩ y ⊆ x
        Sets_intersect_included2:
          forall x y, x ∩ y ⊆ y
      
    例如，我们可以如下证明集合交具有交换律和结合律。*)

Theorem Sets1_intersect_comm:
  forall {A: Type} (x y: A -> Prop),
    x ∩ y == y ∩ x.
Proof.
  intros.
  (** 首先，要证明两个集合相等只需要证明它们互为子集。*)
  apply Sets_equiv_Sets_included; split.
  + (** 第一个分支需要证明_[x ∩ y ⊆ y ∩ x]_，右边是两个集合的交集，因此这两个集合都包
        含左边集合即可。*)
    apply Sets_included_intersect.
    - (** 现在需要证明_[x ∩ y ⊆ y]_，形式上，是要证明左侧两个集合的交集是右侧集合的子
          集，这只需要证明左侧的第二个集合是右侧集合的子集就够了。 *)
      rewrite Sets_intersect_included2.
      reflexivity.
    - (** 类似的，这个子分支需要证明_[x ∩ y ⊆ x]_，我们可以选择将其归结为证明左边的一
          个集合是右边集合的子集。。 *)
      rewrite Sets_intersect_included1.
      reflexivity.
  + (** 第二个分支的证明是类似的。*)
    apply Sets_included_intersect.
    - rewrite Sets_intersect_included2.
      reflexivity.
    - rewrite Sets_intersect_included1.
      reflexivity.
Qed.

Theorem Sets1_intersect_assoc:
  forall {A: Type} (x y z: A -> Prop),
    (x ∩ y) ∩ z == x ∩ (y ∩ z).
Proof.
  intros.
  (** 与证明交集交换律的时候类似，我们将两个集合相等的证明归于为证明它们互为子集。*)
  apply Sets_equiv_Sets_included; split.
  + (** 第一个分支需要证明_[(x ∩ y) ∩ z ⊆ x ∩ (y ∩ z)]_。要证明左侧是右侧三个集合交集
        的子集，就需要证明左侧是右侧每一个集合的子集。*)
    apply Sets_included_intersect; [| apply Sets_included_intersect].
    (** 现在三个证明目标分别是：
        - (x ∩ y) ∩ z ⊆ x
        - (x ∩ y) ∩ z ⊆ y
        - (x ∩ y) ∩ z ⊆ z
        证明时只需要指明左边三个集合中哪一个是右边的子集即可。*)
    - rewrite Sets_intersect_included1.
      rewrite Sets_intersect_included1.
      reflexivity.
    - rewrite Sets_intersect_included1.
      rewrite Sets_intersect_included2.
      reflexivity.
    - rewrite Sets_intersect_included2.
      reflexivity.
  + (** 第二个分支的证明是类似的。*)
    apply Sets_included_intersect; [apply Sets_included_intersect |].
    - rewrite Sets_intersect_included1.
      reflexivity.
    - rewrite Sets_intersect_included2.
      rewrite Sets_intersect_included1.
      reflexivity.
    - rewrite Sets_intersect_included2.
      rewrite Sets_intersect_included2.
      reflexivity.
Qed.

(** 对于并集运算而言，要证明某两个集合的并集包含第三个集合，或者证明某两个集合的并集被
    第三个集合包含，就类似于要证明形如_[P -> Q \/ R]_或_[P \/ Q -> R]_的命题。具体
    地，

        _[x ⊆ y ∪ z]_可以被规约为_[x ⊆ y]_; 

        _[x ⊆ y ∪ z]_也可以被规约为_[x ⊆ z]_; 

        _[x ∪ y ⊆ z]_可以被规约为_[x ⊆ z]_与_[y ⊆ z]_。 

    在Coq中，前两种证明可以通过从右向左_[rewrite]_下面引理实现。
   
        Sets_included_union1:
          forall x y, x ⊆ x ∪ y
        Sets_included_union2:
          forall x y, y ⊆ x ∪ y
      
    而后一种证明则可以通过_[apply]_下面引理实现。
   
        Sets_union_included:
          forall x y z, x ⊆ z -> y ⊆ z -> x ∪ y ⊆ z;
      
    有时，包含号_[⊆]_左侧的集合不是一个并集，需要先使用交集对于并集的分配律才能使用
    _[Sets_union_included]_。*)

(************)
(** 习题：  *)
(************)

(** 请证明下面关于集合的性质。 *)

Fact sets_fact_ex: forall (A: Type) (X Y: A -> Prop),
  X ⊆ Y ->
  X ∩ Y == X.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

(** 请证明下面集合运算的性质。*)

Example Sets1_intersect_absorb_union:
  forall {A: Type} (x y: A -> Prop),
    x ∩ (x ∪ y) == x.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

(** 请证明下面集合运算的性质。*)

Example Sets1_union_absorb_intersect:
  forall {A: Type} (x y: A -> Prop),
    x ∪ (x ∩ y) == x.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(** 总而言之，以下这些SetsClass拓展库中的引理，构成了供我们手动证明集合运算性质的基本
    方法。
   
        Sets_equiv_Sets_included:
          forall x y, x == y <-> x ⊆ y /\ y ⊆ x
        Sets_intersect_included1:
          forall x y, x ∩ y ⊆ x
        Sets_intersect_included2:
          forall x y, x ∩ y ⊆ y
        Sets_included_intersect:
          forall x y z, x ⊆ y -> x ⊆ z -> x ⊆ y ∩ z
        Sets_included_union1:
          forall x y, x ⊆ x ∪ y
        Sets_included_union2:
          forall x y, y ⊆ x ∪ y
        Sets_union_included:
          forall x y z, x ⊆ z -> y ⊆ z -> x ∪ y ⊆ z
        Sets_intersect_union_distr_r:
          forall x y z, (x ∪ y) ∩ z == x ∩ z ∪ y ∩ z
        Sets_intersect_union_distr_l:
          forall x y z, x ∩ (y ∪ z) == x ∩ y ∪ x ∩ z
      
    基于这些引理，我们前面已经证明集合交的交换律与结合律。这些我们演示过的证明都已经包
    含在SetsClass拓展库中了，除此之外，SetsClass拓展库还提供了集合并的交换律与结合
    律以及集合并对集合交左右分配律。SetsClass拓展库中的证明也不限于形如_[A -> Prop]_
    类型的Coq集合，而一并考虑了_[A -> B -> Prop]_、_[A -> B -> C -> Prop]_等所有可
    能的情形。
   
        Sets_intersect_comm:
          forall x y, x ∩ y == y ∩ x
        Sets_intersect_assoc:
          forall x y z, (x ∩ y) ∩ z == x ∩ (y ∩ z)
        Sets_union_comm:
          forall x y, x ∪ y == y ∪ x
        Sets_union_assoc:
          forall x y z, (x ∪ y) ∪ z == x ∪ (y ∪ z)
        Sets_union_intersect_distr_l:
          forall x y z, x ∪ (y ∩ z) == (x ∪ y) ∩ (x ∪ z)
        Sets_union_intersect_distr_r:
          forall x y z, (x ∩ y) ∪ z == (x ∪ z) ∩ (y ∪ z)
      *)

(** ** 空集与全集性质的Coq证明 *)

(** SetsClass拓展库对于空集的支持主要是通过以下性质：空集是一切集合的子集。
   
        Sets_empty_included: forall x, ∅ ⊆ x
      
    相对应的，一切集合都是全集的子集。 
   
        Sets_included_full: forall x, x ⊆ Sets.full
      
    基于这两条性质，可以证明许多有用的导出性质。SetsClass提供的导出性质有：
   
        Sets_union_empty_l: forall x, ∅ ∪ x == x
        Sets_union_empty_r: forall x, x ∪ ∅ == x
        Sets_intersect_empty_l: forall x, ∅ ∩ x == ∅
        Sets_intersect_empty_r: forall x, x ∩ ∅ == ∅
        Sets_union_full_l: forall x, Sets.full ∪ x == Sets.full
        Sets_union_full_r: forall x, x ∪ Sets.full == Sets.full
        Sets_intersect_full_l: forall x, Sets.full ∩ x == x
        Sets_intersect_full_r: forall x, x ∩ Sets.full == x
        Sets_equiv_empty_fact: forall x, x ⊆ ∅ <-> x == ∅
        Sets_equiv_full_fact: forall x, Sets.full ⊆ x <-> x == Sets.full
      *)

(************)
(** 习题：  *)
(************)

(** 前面已经提到，SetsClass拓展库已经证明了_[Sets_intersect_empty_l]_。请你只使用
    _[Sets_empty_included]_以及交集的性质证明它。*)

Lemma Sets1_intersect_empty_l:
  forall (A: Type) (x: A -> Prop), ∅ ∩ x == ∅.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(** ** 补集的性质 *)

(** SetsClass库中提供的关于补集的性质有下面四组。(1) 一个集合与自己的补集求交或求并会
    得到空集或全集。 
   
        Sets_intersect_complement_self
          forall x, x ∩ Sets.complement x == ∅
        Sets_complement_self_intersect
          forall x, Sets.complement x ∩ x == ∅
        Sets_union_complement_self:
          forall x, x ∪ Sets.complement x == Sets.full
        Sets_complement_self_union
          forall x, Sets.complement x ∪ x == Sets.full
      
    (2) 补集的补集是原集合。 
   
        Sets_complement_complement
          forall x, Sets.complement (Sets.complement x) == x
      
    (3) 交集或并集的补集满足德摩根律。 
   
        Sets_complement_union
          forall x y,
            Sets.complement (x ∪ y) ==
            Sets.complement x ∩ Sets.complement y
        Sets_complement_intersect
          forall x y,
            Sets.complement (x ∩ y) ==
            Sets.complement x ∪ Sets.complement y
      
    (4) 补集与包含关系之间满足类似逆否命题之间的性质。 
   
        Sets_contrapositive_PP:
          forall x y, x ⊆ y -> Sets.complement y ⊆ Sets.complement x
        Sets_contrapositive_CC:
          forall x y, Sets.complement y ⊆ Sets.complement x -> x ⊆ y
        Sets_contrapositive_PC:
          forall x y, y ⊆ Sets.complement x -> x ⊆ Sets.complement y
        Sets_contrapositive_CC:
          forall x y, Sets.complement x ⊆ y -> Sets.complement y ⊆ x
      *)

(** ** 无穷交与无穷并的性质 *)

(** SetsClass拓展库提供了两种支持无穷交集和无穷并集的定义。它们的证明方式与普通的并集
    与交集的证明方式是类似的。

    - 基于指标集的集合并：_[⋃ X]_，_[Sets.indexed_union X]_
    
    - 基于指标集的集合交：_[⋂ X]_，_[Sets.indexed_intersect X]_
    
    - 广义并：_[⨆ U]_，_[Sets.general_union U]_
    
    - 广义交：_[⨅ U]_，_[Sets.general_intersect U]_


    它们相关性质的证明方式与普通并集与交集的证明方式是类似的。下面是一个简单的例子。*)

Example Sets1_union_indexed_intersect_fact:
  forall {A: Type} (x: nat -> A -> Prop) (y: A -> Prop),
    (⋂ x) ∪ y ⊆ ⋂ (fun n => x n ∪ y).
Proof.
  intros.
  (** 要证明左边集合是右边这无穷多个集合交集的子集，就需要证明左边集合是右边每一个集合
      的子集。 *)
  apply Sets_included_indexed_intersect.
  intros n.
  (** 现在只需要证明_[⋂ x ∪ y ⊆ x n ∪ y]_。 *)
  rewrite (Sets_indexed_intersect_included n).
  reflexivity.
Qed.

(** * 二元关系与二元关系上的运算 *)



(** SetsClass拓展库中提供了这些关于二元关系的定义：
   
    - 二元关系的连接：用 _[∘]_表示，定义为_[Rels.concat]_；

    - 相等关系：定义为_[Rels.id]_（没有专门的表示符号）；

    - 测试：定义为_[Rels.test]_（没有专门的表示符号）。

    基于此，我们可以将一些二元关系运算的例子写作Coq命题，下面就是一个这样的例子。*)

Fact plus_1_concat_plus_1:
  forall S1 S2: Z -> Z -> Prop,
    (forall n m, (n, m) ∈ S1 <-> m = n + 1) ->
    (forall n m, (n, m) ∈ S2 <-> m = n + 2) ->
    S1 ∘ S1 == S2.
Proof.
  intros S1 S2 H_S1 H_S2.
  Sets_unfold.
  intros x z.
  (** _[Sets_unfold]_指令将_[∘]_的定义展开，现在需要证明：
        - exists y, (x, y) ∈ S1 /\ (y, z) ∈ S1
      当且仅当
        - (x, z) ∈ S2]_。*)
  rewrite H_S2.
  setoid_rewrite H_S1.
  (** 根据_[S1]_与_[S2]_的定义，就只需要证明：
        - (exists y, y = x + 1 /\ z = y + 1) <-> z = x + 2 *)
  split.
  + intros [y [? ?]].
    lia.
  + intros.
    exists (x + 1).
    lia.
Qed.

(** 二元关系除了满足普通集合的运算性质之外，还有几条额外的重要运算性质。

   

    - 结合律：_[(x ∘ y) ∘ z == x ∘ (y ∘ z)]_
    
    - 左单位元：_[Rels.id ∘ x == x]_
    
    - 右单位元：_[x ∘ Rels.id == x]_
    
    - 左分配律：_[x ∘ (y ∪ z) == x ∘ y ∪ x ∘ z]_

    - 右分配律：_[(x ∪ y) ∘ z == x ∘ z ∪ y ∘ z]_


    另外，二元关系对并集的分配律对于无穷并集也成立。这些性质对应了SetsClass库中的下面
    这些定理。*)

