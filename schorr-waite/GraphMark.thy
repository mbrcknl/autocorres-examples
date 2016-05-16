theory GraphMark
imports "~/verification/mainline/l4v/tools/autocorres/AutoCorres"
begin

install_C_file "graph_mark.c"
autocorres [heap_abs_syntax] "graph_mark.c"

definition reach :: "('a \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "reach f roots = rtrancl { p. snd p \<in> f (fst p) } `` roots"

context graph_mark begin

type_synonym state_pred = "lifted_globals \<Rightarrow> bool"

definition ptr_ok :: "node_C ptr \<Rightarrow> state_pred" where
  "ptr_ok p s \<equiv> p \<noteq> NULL \<and> is_valid_node_C s p"

definition out :: "lifted_globals \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr set" where
  "out s p \<equiv> { s[p]\<rightarrow>left, s[p]\<rightarrow>right }"

definition mark :: "bool \<Rightarrow> node_C \<Rightarrow> node_C" where
  "mark c node \<equiv> if c then node \<lparr> mark_C := 3 \<rparr> else node"

definition mark_precondition :: "state_pred \<Rightarrow> node_C ptr \<Rightarrow> state_pred" where
  "mark_precondition P root \<equiv> \<lambda> s. let R = reach (out s) {root} in
    (\<forall> p \<in> R. ptr_ok p s \<and> s[p]\<rightarrow>mark = 0) \<and> P (heap_node_C_update (\<lambda> h p. mark (p \<in> R) (h p)) s)"

primrec roots :: "node_C ptr \<times> node_C ptr \<Rightarrow> node_C ptr set" where
  "roots (p,q) = { r \<in> {p,q}. r \<noteq> NULL }"

type_synonym path_ok_t =
  "lifted_globals \<Rightarrow> lifted_globals \<Rightarrow> node_C ptr set
    \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr list \<Rightarrow> bool "

primrec tail_ok :: path_ok_t where
  "tail_ok s t M r q p [] = (p = NULL \<and> q = r)" |
  "tail_ok s t M r q p (p' # ps) =
    (p = p' \<and>
      ((t[p]\<rightarrow>mark = 1 \<and>
          t[p]\<rightarrow>left = q \<and> t[p]\<rightarrow>right = s[p]\<rightarrow>left \<and> tail_ok s t M r p s[p]\<rightarrow>right ps) \<or>
       (t[p]\<rightarrow>mark = 2 \<and> t[p]\<rightarrow>left \<in> M \<and>
          t[p]\<rightarrow>right = q \<and> t[p]\<rightarrow>left = s[p]\<rightarrow>right \<and> tail_ok s t M r p s[p]\<rightarrow>left ps)))"

primrec path_ok :: path_ok_t where
  "path_ok s t M r q p [] = (p = NULL \<and> q = r)" |
  "path_ok s t M r q p (p' # ps) =
    (p = p' \<and>
      ((t[p]\<rightarrow>mark = 0 \<and>
          t[p]\<rightarrow>left = s[p]\<rightarrow>left \<and> t[p]\<rightarrow>right = s[p]\<rightarrow>right) \<or>
       (t[p]\<rightarrow>mark = 1 \<and> t[p]\<rightarrow>left \<in> M \<and>
          t[p]\<rightarrow>left = q \<and> t[p]\<rightarrow>right = s[p]\<rightarrow>left \<and> tail_ok s t M r p s[p]\<rightarrow>right ps) \<or>
       (t[p]\<rightarrow>mark = 2 \<and> t[p]\<rightarrow>left \<in> M \<and> t[p]\<rightarrow>right \<in> M \<and>
          t[p]\<rightarrow>right = q \<and> t[p]\<rightarrow>left = s[p]\<rightarrow>right \<and> tail_ok s t M r p s[p]\<rightarrow>left ps)))"

primrec mark_invariant :: "state_pred \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr \<times> node_C ptr \<Rightarrow> state_pred" where
  "mark_invariant P root (p,q) s =
    (\<exists> t path M.
      let
        R = reach (out t) {root};
        U = R - M;
        F = U - set path
      in
        P t \<and>
        M = reach (out t) M \<and>
        (\<forall> p \<in> R. ptr_ok p t) \<and>
        (\<forall> p \<in> M. s[p]\<rightarrow>mark = 3) \<and>
        (\<forall> p \<in> F. s[p]\<rightarrow>mark = 0) \<and>
        path_ok s t M root q p path \<and>
        R = reach (out s) (roots (p,q)) \<and>
        t = heap_node_C_update (\<lambda> h p. mark (p \<in> U) (h p)) s)"

primrec mark_measure :: "(node_C ptr \<times> node_C ptr) \<times> lifted_globals \<Rightarrow> nat" where
  "mark_measure (r,s) = setsum (\<lambda> p. 3 - unat s[p]\<rightarrow>mark) (reach (out s) (roots r))"

lemma graph_mark'_correct: "\<lbrace> mark_precondition P root \<rbrace> graph_mark' root \<lbrace> \<lambda> _. P \<rbrace>!"
  unfolding
    graph_mark'_def mark_precondition_def
    whileLoop_add_inv[where I="mark_invariant P root" and M="mark_measure"]
  apply (wp; clarsimp)
  subgoal for p q s t path M sorry
  subgoal for q s t path M sorry
  subgoal for s sorry
  done

end

end
