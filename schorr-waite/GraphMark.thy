theory GraphMark
imports "~/verification/mainline/l4v/tools/autocorres/AutoCorres"
begin

install_C_file "graph_mark.c"
autocorres [heap_abs_syntax] "graph_mark.c"

definition f_star :: "('a \<Rightarrow> 'a set) \<Rightarrow> ('a \<Rightarrow> 'a set)" where
  "f_star f p = rtrancl { p. snd p \<in> f (fst p) } `` { p }"

context graph_mark begin

definition ok :: "node_C ptr \<Rightarrow> lifted_globals \<Rightarrow> bool" where
  "ok p s \<equiv> p \<noteq> NULL \<and> is_valid_node_C s p"

definition reach :: "lifted_globals \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr set" where
  "reach s \<equiv> f_star (\<lambda> p. { s[p]\<rightarrow>left, s[p]\<rightarrow>right })"

definition mark :: "bool \<Rightarrow> node_C \<Rightarrow> node_C" where
  "mark c node \<equiv> if c then node \<lparr> mark_C := 3 \<rparr> else node"

lemma graph_mark'_correct:
  "\<lbrace> \<lambda> s. s = i \<and> (\<forall> p \<in> reach s root. ok p s \<and> s[p]\<rightarrow>mark = 0) \<rbrace>
    graph_mark' root
   \<lbrace> \<lambda> _ s. s = heap_node_C_update (\<lambda> h p. mark (p \<in> reach s root) (h p)) i \<rbrace>!"
  unfolding
    graph_mark'_def
  sorry

end

end
