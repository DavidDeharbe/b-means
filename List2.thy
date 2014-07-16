theory List2

imports Main

begin

subsection {* Auxiliary properties on (pairs of) lists *}

text {* The following gives an alternative definition to @{text "list_all2"} to define a predicate
that applies to the elements of two lists, position-wise. It is defined recursively on the
structure of the lists (instead of using sets as in the standard library definition). *}

inductive all :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> bool"
where
  nil[intro!]:  "all p [] []" | 
  cons[intro!]: "\<lbrakk> p v1 v2; all p l1 l2 \<rbrakk> \<Longrightarrow> all p (v1 # l1) (v2 # l2)"

inductive_cases all_not_empty [elim!]: "all p (v1 # l1) (v2 # l2)"

lemma empty: "\<lbrakk> all p l1 l2 \<rbrakk> \<Longrightarrow> (l1 = [] \<longleftrightarrow> l2 = [])"
proof(induct rule:all.induct, simp, simp)
qed

lemma last: 
  "\<lbrakk> all (p :: 'a \<Rightarrow> 'b \<Rightarrow> bool) (l1 :: 'a list) (l2 :: 'b list); l1 \<noteq> []; l2 \<noteq> [] \<rbrakk>
     \<Longrightarrow> p (last l1) (last l2)"
proof(induct rule:all.induct, simp)
  show "\<And>p v1 v2 l1 l2.
       (p :: 'a \<Rightarrow> 'b \<Rightarrow> bool) v1 v2 \<Longrightarrow>
       all p l1 l2 \<Longrightarrow>
       (l1 \<noteq> [] \<Longrightarrow> l2 \<noteq> [] \<Longrightarrow> p (last l1) (last l2)) \<Longrightarrow>
       v1 # l1 \<noteq> [] \<Longrightarrow> v2 # l2 \<noteq> [] \<Longrightarrow> p (last (v1 # l1)) (last (v2 # l2))"
  proof-
    fix p v1 v2 l1 l2
    assume "(p :: 'a \<Rightarrow> 'b \<Rightarrow> bool) v1 v2" "all p l1 l2"
      "(l1 \<noteq> [] \<Longrightarrow> l2 \<noteq> [] \<Longrightarrow> p (last l1) (last l2))"
      "v1 # l1 \<noteq> []" "v2 # l2 \<noteq> []"
    show "p (last (v1 # l1)) (last (v2 # l2))"
    proof(case_tac l1)
      assume "l1 = []"
      from `l1 = []` `all p l1 l2` have "l2 = []" by (simp add:empty)
      from `l1 = []` `l2 = []` `p v1 v2`
      show "p (last (v1 # l1)) (last (v2 # l2))" by simp
    next
      fix a list
      assume "l1 = a # list"
      then have "l1 \<noteq> []" by simp
      then have "last (v1 # l1) = last l1" by (simp)
    moreover
      from `l1 \<noteq> []` and `all p l1 l2` have "l2 \<noteq> []" by (simp add:empty)
      then have "last (v2 # l2) = last l2" by (simp)
    moreover
      from `l1 \<noteq> []` and `l2 \<noteq> []` and `(l1 \<noteq> [] \<Longrightarrow> l2 \<noteq> [] \<Longrightarrow> p (last l1) (last l2))`
      have "p (last l1) (last l2)" by simp
    ultimately
      show "p (last (v1 # l1)) (last (v2 # l2))" by simp
    qed
  qed
qed

end

