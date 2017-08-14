The Formalization of the Semantics of the Attack Tree Linear Logic
-------------------------------------------------------------------

* Quaternary Lineale Semantics
  - [The Lineale Four](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale.agda)
    - [Sequential Conjunction](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale.agda#L77)
    - [Parallel Conjunction](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale.agda#L65)
    - [Choice](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale.agda#L53)
    - [Tensor Product](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale.agda#L26)
    - [Unit of the Tensor Product](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale.agda#L38)
    - [Linear Implication](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale.agda#L41)
    - [Preorder](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale.agda#L17)
  - [Theorems about the Lineale Four](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda)
    - [Reflexivity](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L6) and [transitivity](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L12) of the preorder
    - [Symmetry of the preorder implies equivalence](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L78) and [vice versa](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L96)
    - Theorems about Parallel Conjunction
      - [The left zero theorem](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L114) and [the right zero theorem](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L120)
      - [Contraction implies false](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L126)
      - [Symmetry](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L130), [Associtivity](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L148), and [Functorality](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L214)
    - Theorems about Sequential Conjunction
      - [Symmetry implies false](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L604)
      - [Contraction implies false](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L608)
      - [The left zero theorem](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L612) and [the right zero theorem](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L618)
      - [Associtivity](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L624) and [Functorality](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L690)      
    - Theorems about Choice
      - [Associtivity](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L1098), [Symmetry](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L1080), and [Functorality](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L1164)
      - [Contraction](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L1422)
    - Theorems about the Tensor Product
      - [Associtivity](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L1719), [Symmetry](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L1701), and [Functorality](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L1428)
      - The [left unitor](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L1689) and the [right unitor](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L1695)
      - [Lineale Compatibility](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L1686)
    - Theorems about Linear Implications
      - [Functorality](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L1785)
      - [Currying](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L2042) and [Uncurrying](https://github.com/MonoidalAttackTrees/ATLL-Formalization/blob/master/lineale-thms.agda#L2109)
    - [Interpretation of Attack Trees]()
      