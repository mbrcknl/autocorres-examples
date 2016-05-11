theory GraphMark
imports "~/verification/mainline/l4v/tools/autocorres/AutoCorres"
begin

install_C_file "graph_mark.c"
autocorres [heap_abs_syntax] "graph_mark.c"

definition reach :: "('a \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "reach f roots = rtrancl { p. snd p \<in> f (fst p) } `` roots"

context graph_mark begin

type_synonym state_pred = "lifted_globals \<Rightarrow> bool"

definition ok :: "node_C ptr \<Rightarrow> state_pred" where
  "ok p s \<equiv> p \<noteq> NULL \<and> is_valid_node_C s p"

definition out :: "lifted_globals \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr set" where
  "out s p \<equiv> { s[p]\<rightarrow>left, s[p]\<rightarrow>right }"

definition mark :: "bool \<Rightarrow> node_C \<Rightarrow> node_C" where
  "mark c node \<equiv> if c then node \<lparr> mark_C := 3 \<rparr> else node"

definition mark_pre :: "state_pred \<Rightarrow> node_C ptr \<Rightarrow> state_pred" where
  "mark_pre P root \<equiv> \<lambda> s. let R = reach (out s) {root} in
    (\<forall> p \<in> R. ok p s \<and> s[p]\<rightarrow>mark = 0) \<and> P (heap_node_C_update (\<lambda> h p. mark (p \<in> R) (h p)) s)"

primrec mark_invariant :: "state_pred \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr \<times> node_C ptr \<Rightarrow> state_pred" where
  "mark_invariant P root (p,q) s = True"

primrec roots :: "node_C ptr \<times> node_C ptr \<Rightarrow> node_C ptr set" where
  "roots (p,q) = { r \<in> {p,q}. r \<noteq> NULL }"

primrec mark_measure :: "(node_C ptr \<times> node_C ptr) \<times> lifted_globals \<Rightarrow> nat" where
  "mark_measure (r,s) = setsum (\<lambda> p. 3 - unat s[p]\<rightarrow>mark) (reach (out s) (roots r))"

lemma graph_mark'_correct: "\<lbrace> mark_pre P root \<rbrace> graph_mark' root \<lbrace> \<lambda> _. P \<rbrace>!"
  unfolding
    graph_mark'_def mark_pre_def
    whileLoop_add_inv[where I="mark_invariant P root" and M="mark_measure"]
  apply (wp; clarsimp)
  sorry

end

end
