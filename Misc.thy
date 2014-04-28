(*  Title:      Misc.thy
    Author:     David
*)

header {* Miscellaneous helpful lemmas *}

theory "Misc"
imports Main
begin

lemma relcomp_totality:
  assumes r1_total: "\<forall> x \<in> X. \<exists> y \<in> Y. (x, y) \<in> r1" and r2_total: "\<forall> y \<in> Y . \<exists> z \<in> Z . (y, z) \<in> r2" 
  shows "\<forall> x \<in> X . \<exists> y \<in> Z . (x, y) : r1 O r2"
proof
  fix a
  assume da: "a \<in> X"
  show "\<exists> y \<in> Z . (a, y) : r1 O r2"
  proof -
    from r1_total and da obtain b where witness1: "b \<in> Y \<and> (a, b) \<in> r1" by auto
  moreover
    from witness1 have db: "b \<in> Y" by (rule conjE)
    from r2_total and db obtain c where witness2: "c \<in> Z \<and> (b, c) : r2" by auto
  moreover
    from witness2 have dc: "c \<in> Z" by (rule conjE)
  moreover
    from witness1 and witness2 have witness: "(a, c) \<in> r1 O r2" by auto
    from witness2 and witness show ?thesis by auto
  qed  
qed

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
  moreover
    from w1 have db: "b : Y" by (rule conjE)
    with g2 obtain c where w2: "c \<in> Z \<and> (f b, f c) \<in> s \<and> (g b, g c) \<in> s \<and> h b = h c" by auto
  moreover
    from w2 have dc: "c \<in> Z" by (rule conjE)
  moreover
    from w1 and w2 have w: "(f a, f c) \<in> r O s \<and> (g a, g c) \<in> r O s \<and> h a = h c" by auto
    with dc show ?thesis by auto
  qed
qed

end

