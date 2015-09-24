(*  Title:      Misc.thy
    Author:     David
*)

section {* Miscellaneous helpful lemmas *}

theory "Misc"
imports Main
begin

text {* This is an auxiliary theory, containing lemmas on binary relations. They are used in
the proofs on properties of refinements. *}

text {* The following lemma states that the composition of two total relations is a total relation: *}

lemma relcomp_totality:
  assumes r_total: "\<forall> x \<in> X. \<exists> y \<in> Y. (x, y) \<in> r" and s_total: "\<forall> y \<in> Y . \<exists> z \<in> Z . (y, z) \<in> s" 
  shows "\<forall> x \<in> X . \<exists> z \<in> Z . (x, z) : r O s"
proof
  fix a
  assume da: "a \<in> X"
  show "\<exists> y \<in> Z . (a, y) : r O s"
  proof -
    from r_total and da obtain b where witness1: "b \<in> Y \<and> (a, b) \<in> r" by auto
    then have db: "b \<in> Y" by (rule conjE)
    with s_total obtain c where witness2: "c \<in> Z \<and> (b, c) : s" by auto
    then have dc: "c \<in> Z" by (rule conjE)
    from witness1 and witness2 have witness: "(a, c) \<in> r O s" by auto
    with dc show ?thesis by auto
  qed  
qed

text {* The next lemma is much more specific. It also addresses a property of the composition of 
binary relations that is used a transitivity property for refinements. *}
lemma relcomp_pair:
  assumes
    g1: "\<forall>x\<in>X. \<exists>y\<in>Y. (f x, f y) \<in> r \<and> (g x, g y) \<in> r \<and> h x = h y" and
    g2: "\<forall>y\<in>Y. \<exists>z\<in>Z. (f y, f z) \<in> s \<and> (g y, g z) \<in> s \<and> h y = h z"
  shows
    "\<forall>x\<in>X. \<exists>z\<in>Z. (f x, f z) \<in> r O s \<and> (g x, g z) \<in> r O s \<and> h x = h z"
proof
  fix a
  assume da: "a \<in> X"
  show "\<exists> z \<in> Z . (f a, f z) \<in> r O s \<and> (g a, g z) \<in> r O s \<and> h a = h z"
  proof -
    from g1 and da obtain b where w1: "b \<in> Y \<and>(f a, f b) \<in> r \<and> (g a, g b) \<in> r \<and> h a = h b" by auto
    then have db: "b : Y" by (rule conjE)
    with g2 obtain c where w2: "c \<in> Z \<and> (f b, f c) \<in> s \<and> (g b, g c) \<in> s \<and> h b = h c" by auto
    then have dc: "c \<in> Z" by (rule conjE)
    from w1 and w2 have w: "(f a, f c) \<in> r O s \<and> (g a, g c) \<in> r O s \<and> h a = h c" by auto
    with dc show ?thesis by auto
  qed
qed

lemma set_union_elem: "S = \<Union> { { s } | s . s \<in> S }"
  by blast

lemma set_img_union_elem: "r `` S = \<Union> { r `` { s } | s . s \<in> S }"
  by blast

lemma "\<forall> s \<in> S . r `` { s } \<subseteq> R \<Longrightarrow> r `` S \<subseteq> R" 
  by auto

lemma relcomp_witness : "\<forall> (x, y) \<in> r O s . \<exists> z . (x, z) \<in> r \<and> (z, y) \<in> s"
  unfolding relcomp_def by auto

lemma "S = Collect (\<lambda> x . x \<in> S)"
  by simp

end

