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

type_synonym path_upd_t =
  "lifted_globals \<Rightarrow> node_C ptr set
    \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr list \<Rightarrow> lifted_globals option"

primrec tail_upd :: path_upd_t where
  "tail_upd s M r q p [] = (if p = NULL \<and> q = r then Some s else None)" |
  "tail_upd s M r q p (p' # ps) =
   (if p \<noteq> p' then None
    else if s[p]\<rightarrow>mark = 1 then
      tail_upd s[p\<rightarrow>left := q][p\<rightarrow>right := s[p]\<rightarrow>left] M r p s[p]\<rightarrow>right ps
    else if s[p]\<rightarrow>mark = 2 \<and> s[p]\<rightarrow>right \<in> M then
      tail_upd s[p\<rightarrow>right := q][p\<rightarrow>left := s[p]\<rightarrow>right] M r p s[p]\<rightarrow>left ps
    else None)"

primrec path_upd :: path_upd_t where
  "path_upd s M r q p [] = (if p = NULL \<and> q = r then Some s else None)" |
  "path_upd s M r q p (p' # ps) =
   (if p \<noteq> p' then None
    else if s[p]\<rightarrow>mark = 0 then
      tail_upd s M r p q ps
    else if s[p]\<rightarrow>mark = 1 \<and> q \<in> M then
      tail_upd s[p\<rightarrow>left := q][p\<rightarrow>right := s[p]\<rightarrow>left] M r p s[p]\<rightarrow>right ps
    else if s[p]\<rightarrow>mark = 2 \<and> s[p]\<rightarrow>right \<in> M \<and> q \<in> M then
      tail_upd s[p\<rightarrow>right := q][p\<rightarrow>left := s[p]\<rightarrow>right] M r p s[p]\<rightarrow>left ps
    else None)"

primrec mark_invariant :: "state_pred \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr \<times> node_C ptr \<Rightarrow> state_pred" where
  "mark_invariant P root (p,q) s =
    (\<exists> t u path M.
      let
        R = reach (out t) {root};
        U = R - M;
        F = U - set path
      in
        P t \<and>
        Some u = path_upd s M root q p path \<and>
        t = heap_node_C_update (\<lambda> h p. mark (p \<in> U) (h p)) u \<and>
        R = reach (out s) (roots (p,q)) \<and>
        M = reach (out t) M \<and>
        (\<forall> p \<in> R. ptr_ok p s) \<and>
        (\<forall> p \<in> M. s[p]\<rightarrow>mark = 3) \<and>
        (\<forall> p \<in> F. s[p]\<rightarrow>mark = 0))"

primrec mark_measure :: "(node_C ptr \<times> node_C ptr) \<times> lifted_globals \<Rightarrow> nat" where
  "mark_measure (r,s) = setsum (\<lambda> p. 3 - unat s[p]\<rightarrow>mark) (reach (out s) (roots r))"

lemma graph_mark'_correct: "\<lbrace> mark_precondition P root \<rbrace> graph_mark' root \<lbrace> \<lambda> _. P \<rbrace>!"
  unfolding
    graph_mark'_def mark_precondition_def
    whileLoop_add_inv[where I="mark_invariant P root" and M="mark_measure"]
  apply (wp; clarsimp)
  subgoal for p q s t u path M
   sorry
  subgoal for q s t u path M
   sorry
  subgoal for s
   sorry
  done

end

end
