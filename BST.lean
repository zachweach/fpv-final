import LoVe.LoVelib

namespace LoVe

-- key value pairs are ℕ × α
inductive BST (α : Type)
| leaf                                                 : BST α
| node (val : ℕ × α) (lchild : BST α) (rchild : BST α) : BST α

namespace BST

def testTree : BST ℕ :=
  node (3, 3)
    (node (1, 1) leaf leaf)
    (node (7, 7)
      (node (6, 6)
        (node (5, 5) leaf leaf)
        leaf
      )
      (node (9, 9) leaf leaf)
    )

--     3
--   1   7
--      6 9
--     5

------------------------------------------------------------
--------------------     OPERATIONS     --------------------
------------------------------------------------------------

-- given a tree, insert that value into the tree (lower keys
-- are in the left branches)
def insert {α : Type} (t : BST α) (ival : ℕ × α) : BST α :=
  match t with
  | leaf => node ival leaf leaf
  | node nval left right =>
    if ival.fst < nval.fst then
      node nval (left.insert ival) right
    else if ival.fst > nval.fst then
      node nval left (right.insert ival)
    else -- duplicate key, replaces value stored
      node ival left right

-- gets the value stored at a given key if one exists
def get {α : Type} (t : BST α) (key : ℕ) : Option α :=
  match t with
  | leaf => none
  | node nval left right =>
    if key < nval.fst then
      left.get key
    else if key > nval.fst then
      right.get key
    else
      some nval.snd

#eval get testTree 3 -- some 3
#eval get testTree 9 -- some 9
#eval get testTree 0 -- none

-- finds the minimum value in the tree. if the tree is a leaf,
-- retuns the defualt value
def findMinOrElse {α : Type} (t : BST α) (default : ℕ × α) : ℕ × α :=
  match t with
  | leaf         => default
  | node val l _ =>
    match l with
    | leaf       => val
    | node _ _ _ => findMinOrElse l default

#eval findMinOrElse testTree (0, 0) -- (1, 1)

-- deletes the data associated with the given key from the tree.
-- should keep the tree valid
def delete {α : Type} (t : BST α) (key : ℕ) : BST α :=
  match t with
  | leaf => leaf
  | node val left right =>
    if key < val.fst then
      -- node is in the left branch
      node val (delete left key) right
    else if key > val.fst then
      -- node is in the right branch
      node val left (delete right key)
    else
      -- delete this node
      match left, right with
      | leaf, _  => right
      | _, leaf  => left
      | _, _     => -- node and node
        let low := findMinOrElse right val -- will presumably never use default, since we're in node branch
        node low left (delete right low.fst)


------------------------------------------------------------
--------------------    DEFINITIONS     --------------------
------------------------------------------------------------

-- hold if the given key exists anywhere in the tree. leaves
-- do not contain keys
inductive inTree {α : Type} (key : ℕ) : BST α → Prop
  | eq    val left right (heq : val.fst = key)     : inTree key (node val left right)
  | left  val left right (hinL : inTree key left)  : inTree key (node val left right)
  | right val left right (hinR : inTree key right) : inTree key (node val left right)

-- hold if the tree is a leaf or if it's key value is less than
-- the given value `n`
inductive lessThanOrLeaf {α : Type} (n : ℕ) : BST α → Prop
  | leaf                          : lessThanOrLeaf n leaf
  | node v l r (hvls : v.fst < n) : lessThanOrLeaf n (node v l r)

-- hold if the tree is a leaf or if it's key value is greater
-- than the given value `n`
inductive greaterThanOrLeaf {α : Type} (n : ℕ) : BST α → Prop
  | leaf                          : greaterThanOrLeaf n leaf
  | node v l r (hvgn : v.fst > n) : greaterThanOrLeaf n (node v l r)

-- the canonical "well-formed tree" property. the left side of
-- the tree should contain values lower than the right side
inductive valid {α : Type} : BST α → Prop where
  | leaf : valid leaf
  | node v left right
      (hlless : lessThanOrLeaf v.fst left)
      (hrgreater : greaterThanOrLeaf v.fst right)
      (hlvalid : valid left) (hrvalid : valid right) :
    valid (node v left right)


------------------------------------------------------------
--------------------       PROOFS       --------------------
------------------------------------------------------------

-- if a given tree is valid, then its children must be valid
-- too this is sort of trivial now, after i changed the format
-- of `lessThanOrLeaf` and `greaterThanOrLeaf` to better match
-- how i needed to use them
theorem validChildren {α : Type} (v : ℕ × α) (left right : BST α)
  (hvalid : valid (node v left right))
  : valid left ∧ valid right :=
  by
    cases' hvalid with _ _ _ _ _ hlv hrv
    exact And.intro hlv hrv

-- if a given key is in the tree, then it must either be the
-- key at the root or in one of the children. once again, this
-- also became sort of trivial after i changed the format of
-- `inTree` to be an inductive definiton
theorem inTreeSomewhere {α : Type} (key : ℕ) (v : ℕ × α) (left right : BST α)
  (hin : inTree key (node v left right)) :
  inTree key left ∨ inTree key right ∨ v.fst = key :=
  by
    cases' hin
    apply Or.inr; apply Or.inr; assumption
    apply Or.inl; assumption
    apply Or.inr; apply Or.inl; assumption

-- if a given key exists in one of the children of a node, then
-- it also must exist in the root node as well
theorem inChildrenInTree {α : Type} (key : ℕ) (v : ℕ × α) (left right : BST α)
  (hin : inTree key left ∨ inTree key right) :
  inTree key (node v left right) :=
  by
    cases' hin with hinl hinr
    apply inTree.left _ _ _ hinl
    apply inTree.right _ _ _ hinr

-- if a given key does not exist in a tree, then it does not
-- exist in either child
theorem notInChildren {α : Type} (key : ℕ) (v : ℕ × α) (left right : BST α)
  (hnotin : ¬ inTree key (node v left right)) :
  ¬ (inTree key left) ∧ ¬(inTree key right) :=
  by
    apply And.intro
    {
      intro hinl
      apply hnotin
      exact inChildrenInTree key v left right (Or.inl hinl)
    }
    {
      intro hinr
      apply hnotin
      exact inChildrenInTree key v left right (Or.inr hinr)
    }

-- `insert`ing maintains valid tree
theorem insertValid {α : Type} (t : BST α) (n : ℕ) (a : α)
  : valid t → valid (insert t (n, a)) :=
  by
    intro vt
    induction' t with v l r hlinsvalid hrinsvalid
    {
      exact valid.node _ _ _ (lessThanOrLeaf.leaf) (greaterThanOrLeaf.leaf) valid.leaf valid.leaf
    }
    {
      simp [insert]
      if hlt : n < v.fst then
        simp [hlt]
        cases' vt with _ _ _ hlless hgr hlv hrv
        apply valid.node
        {
          cases' hlless with lv _ _ hllv
          {
            apply lessThanOrLeaf.node
            apply hlt
          }
          {
            rw [insert]
            if h1 : n < lv.fst then
              simp [h1]
              apply lessThanOrLeaf.node
              apply hllv
            else if h2 : n > lv.fst then
              simp [h1, h2]
              apply lessThanOrLeaf.node
              apply hllv
            else
              simp [h1, h2]
              apply lessThanOrLeaf.node
              simp_all
          }
        }
        {
          exact hgr
        }
        {
          apply hlinsvalid
          apply (validChildren v l r _).left
          apply valid.node _ _ _ hlless hgr hlv hrv
          -- apply (notInChildren n v l r nit vt).left
        }
        {
          apply hrv
        }
      else --if hgr : n > v.fst then
        aesop -- i'm not sure *exactly* what this aesop is doing but it gets the goal state i want with the if/else block :P
        apply valid.node
        {
          cases' vt with _ _ _ hlless g t h
          cases' hlless with lv _ _ hllv
          {
            apply lessThanOrLeaf.node
            assumption
          }
          {
            rw [insert]
            if h1 : n < lv.fst then
              simp [h1]
              apply lessThanOrLeaf.node
              apply hllv
            else if h2 : n > lv.fst then
              simp [h1, h2]
              apply lessThanOrLeaf.node
              apply hllv
            else
              simp [h1, h2]
              apply lessThanOrLeaf.node
              simp_all
          }
        }
        {
          cases' vt with _ _ _ _ hgr
          exact hgr
        }
        {
          apply hlinsvalid
          apply (validChildren v l r vt).left
          -- apply (notInChildren n v l r nit vt).left
        }
        {
          cases' vt with _ _ _ _ _ _ hrv
          apply hrv
        }
        {
          cases' vt with _ _ _ hll hgr hvl hvr
          apply valid.node
          {
            exact hll
          }
          {
            cases' hgr with rv _ _ hvgn
            {
              apply greaterThanOrLeaf.node
              assumption
            }
            {
              rw [insert]
              if h1 : n < rv.fst then
                simp [h1]
                apply greaterThanOrLeaf.node
                apply hvgn
              else if h2 : n > rv.fst then
                simp [h1, h2]
                apply greaterThanOrLeaf.node
                apply hvgn
              else
                simp [h1, h2]
                apply greaterThanOrLeaf.node
                simp_all
            }
          }
          {
            exact hvl
          }
          apply hrinsvalid hvr
          -- apply (notInChildren n v l r nit (valid.node _ _ _ hll hgr hvl hvr)).right
        }
        {
          cases' vt with _ _ _ hl hg
          apply valid.node
          {
            cases' hl
            apply lessThanOrLeaf.leaf
            apply lessThanOrLeaf.node
            linarith
          }
          {
            cases' hg
            apply greaterThanOrLeaf.leaf
            apply greaterThanOrLeaf.node
            linarith
          }
          all_goals assumption
        }
    }

-- given a valid tree, `insert`ing any value into that tree
-- means that key will appear in the tree
theorem insertInTree {α : Type} (t : BST α) (n : ℕ) (a : α)
  : valid t → inTree n (insert t (n, a)) :=
  by
    intro hvt
    induction' t with v l r
    all_goals rw [insert]
    {
      apply inTree.eq
      rfl
    }
    {
      cases' hvt
      aesop -- breaking the if/elses into cases
      {
        apply inTree.left
        apply insertInTree
        assumption
      }
      {
        apply inTree.right
        apply insertInTree
        assumption
      }
      {
        apply inTree.eq
        rfl
      }
    }
    done

-- `delete`ing maintains valid tree
theorem deleteValid {α : Type} (t : BST α) (n : ℕ)
  : valid t → valid (delete t n) :=
  by
    intro vt
    induction' t with v l r hlinsvalid hrinsvalid
    {
      apply valid.leaf
    }
    {
      simp [delete]
      if hnlt: n < v.fst then
        simp_all
        cases' vt with _ _ _ hlless hgr hlv hrv
        apply valid.node
        {
          cases' hlless with lv ll lr hllv
          {
            exact lessThanOrLeaf.leaf
          }
          {
            rw [delete]
            if h1 : n < lv.fst then
              simp [h1]
              apply lessThanOrLeaf.node
              apply hllv
            else if h2 : n > lv.fst then
              simp [h1, h2]
              apply lessThanOrLeaf.node
              apply hllv
            else
              sorry
          }
        }
        {
          exact hgr
        }
        {
          apply hlinsvalid hlv
        }
        {
          exact hrv
        }
      else if hvlt: v.fst < n then
        simp [hnlt, hvlt]
        cases' vt with _ _ _ hlless hgr hlv hrv
        apply valid.node
        {
          exact hlless
        }
        {
          cases' hgr with rv
          {
            exact greaterThanOrLeaf.leaf
          }
          {
            rw [delete]
            if h1 : n < rv.fst then
              simp [h1]
              apply greaterThanOrLeaf.node
              assumption
            else if h2 : n > rv.fst then
              simp [h1, h2]
              apply greaterThanOrLeaf.node
              assumption
            else
              sorry
          }
        }
        {
          exact hlv
        }
        {
          apply hrinsvalid hrv
        }
      else
        simp [hnlt, hvlt]
        cases' l with lv ll lr
        {
          simp
          apply (validChildren v leaf r vt).right
        }
        {
          cases' r
          {
            simp
            apply (validChildren v (node lv ll lr) leaf vt).left
          }
          {
            simp
            sorry
            -- apply valid.node
            -- {
            --   apply lessThanOrLeaf.node
            -- }
          }
        }
    }

-- given a valid tree, `insert`ing any value into that tree
-- then `delete`ing that same value will result in the same
-- tree
--    NOT TRUE: duplicates
theorem insertDelete {α : Type} (t : BST α) (n : ℕ) (a : α)
  : valid t → t = delete (insert t (n, a)) n := sorry

-- if the tree is empty, the above property is true
theorem insertDeleteEmpty {α : Type} (t : BST α) (n : ℕ) (a : α)
  (htempty : t = leaf)
  : valid t → t = delete (insert t (n, a)) n :=
  by
    rw [htempty, insert, delete]
    simp

-- if the tree does not contain `n`, the above property is true
-- theoretically this is true, since the duplicates problem from
-- before is gone, since `n` is not in the tree. formalization TBD
theorem insertDeleteNotIn {α : Type} (t : BST α) (n : ℕ) (a : α)
  : valid t → ¬inTree n t → t = delete (insert t (n, a)) n :=
  by
    intro vt nit
    induction' t with v l r hlinsvalid hrinsvalid
    {
      apply insertDeleteEmpty
      rfl
      assumption
    }
    {
      rw [insert]
      if hnl : n < v.fst then
        sorry
      else if hng : n > v.fst then
        sorry
      else
        simp [hnl, hng]
        rw [delete]
        sorry
    }


end BST

end LoVe
