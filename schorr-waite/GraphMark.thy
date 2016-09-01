theory GraphMark
imports "~/verification/mainline/l4v/tools/autocorres/AutoCorres"
begin

section {* Reachability *}

text {*
  Given a type \emph{'a} of pointers to nodes, a function \emph{e} which takes a pointer into a
  node to the set of pointers out of that node, a set \emph{N} of pointers which should not be
  traversed, and a set \emph{R} of pointers to root objects, then \emph{reach e N R} inductively
  defines the set of pointers to nodes that are reachable by \emph{e} from \emph{R}, without
  traversing pointers in \emph{N}. The set \emph{N} typically contains some distinguished pointer,
  such as the null pointer.
*}

inductive_set reach :: "('a \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  for e :: "'a \<Rightarrow> 'a set" and N :: "'a set" and R :: "'a set"
  where
    reach_root[intro]: "p \<in> R \<Longrightarrow> p \<notin> N \<Longrightarrow> p \<in> reach e N R"
  | reach_step[intro]: "p \<in> reach e N R \<Longrightarrow> q \<in> e p \<Longrightarrow> q \<notin> N \<Longrightarrow> q \<in> reach e N R"

section {* Specification *}

install_C_file "graph_mark.c"
autocorres [heap_abs_syntax] "graph_mark.c"

context graph_mark begin

type_synonym mark = "32 word"
type_synonym state_pred = "lifted_globals \<Rightarrow> bool"

definition out :: "lifted_globals \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr set" where
  "out s p \<equiv> { s[p]\<rightarrow>left, s[p]\<rightarrow>right }"

definition mark_set :: "mark \<Rightarrow> node_C ptr set \<Rightarrow> lifted_globals \<Rightarrow> lifted_globals" where
  "mark_set m R \<equiv> heap_node_C_update (\<lambda> h p. mark_C_update (If (p \<in> R) m) (h p))"

definition mark_precondition :: "state_pred \<Rightarrow> node_C ptr \<Rightarrow> state_pred" where
  "mark_precondition P root \<equiv> \<lambda> s.
    let R = reach (out s) {NULL} {root} in
      (\<forall> p \<in> R. is_valid_node_C s p \<and> s[p]\<rightarrow>mark = 0) \<and> P (mark_set 3 R s)"

definition mark_specification :: "state_pred \<Rightarrow> node_C ptr \<Rightarrow> bool" where
  "mark_specification P root \<equiv> \<lbrace> mark_precondition P root \<rbrace> graph_mark' root \<lbrace> \<lambda> _. P \<rbrace>!"

-- "Proof"

abbreviation (input) reach_p :: "lifted_globals \<Rightarrow> node_C ptr set \<Rightarrow> node_C ptr set" where
  "reach_p s R \<equiv> reach (out s) {NULL} R"

definition mark_incr :: "node_C ptr \<Rightarrow> lifted_globals \<Rightarrow> lifted_globals" where
  "mark_incr p \<equiv> heap_node_C_update (\<lambda> h. h(p := mark_C_update (\<lambda> m. m + 1) (h p)))"

lemma mark_incr_mark [simp]: "(mark_incr q s)[p]\<rightarrow>mark = s[p]\<rightarrow>mark + (if p = q then 1 else 0)"
  unfolding mark_incr_def by (simp add: fun_upd_def graph_mark.get_node_mark_def)

end

locale link_read_stable =
  fixes
    f :: "lifted_globals \<Rightarrow> lifted_globals"
  assumes
    read_stable_l [simp]: "\<And> p. (f s)[p]\<rightarrow>left = s[p]\<rightarrow>left" and
    read_stable_r [simp]: "\<And> p. (f s)[p]\<rightarrow>right = s[p]\<rightarrow>right" and
    read_stable_v [simp]: "\<And> p. is_valid_node_C (f s) p = is_valid_node_C s p"

context link_read_stable begin

sublocale graph_mark .

lemma out_link_read_stable [simp]: "out (f s) = out s"
  unfolding out_def[abs_def] by fastforce

end

context graph_mark begin

sublocale mark_incr_link_read_stable?: link_read_stable "mark_incr q"
  apply unfold_locales
  by (auto simp: mark_incr_def fun_upd_def
                 graph_mark.get_node_left_def graph_mark.get_node_right_def)

sublocale mark_set_link_read_stable?: link_read_stable "mark_set m R"
  apply unfold_locales
  by (auto simp: mark_set_def fun_upd_def
                 graph_mark.get_node_left_def graph_mark.get_node_right_def)

lemma mark_incr_ptr_upd:
  "(mark_incr q s)[p\<rightarrow>left := v] = mark_incr q s[p\<rightarrow>left := v]"
  "(mark_incr q s)[p\<rightarrow>right := v] = mark_incr q s[p\<rightarrow>right := v]"
  unfolding mark_incr_def
  by (smt fun_upd_def fun_upd_twist fun_upd_upd
          graph_mark.update_node_left_def graph_mark.update_node_right_def
          lifted_globals.surjective lifted_globals.update_convs(5) node_C_updupd_diff(1,2))+

lemma reach_subset: assumes "R \<subseteq> S" shows "reach e N R \<subseteq> reach e N S"
  proof -
    { fix p have "p \<in> reach e N R \<Longrightarrow> R \<subseteq> S \<Longrightarrow> p \<in> reach e N S"
      by (induction rule: reach.induct) auto }
    thus ?thesis using assms by auto
  qed

lemma reachable_excluded:
  assumes "R \<subseteq> N"
  shows "reach e N R = {}"
  proof -
    { fix p have "p \<in> reach e N R \<Longrightarrow> \<not> R \<subseteq> N"
      by (induction rule: reach.induct) auto }
    thus ?thesis using assms by auto
  qed

lemmas reachable_excluded_simps [simp] =
  reachable_excluded[of "{}" N for N, simplified]
  reachable_excluded[of N N for N, simplified]

lemma reach_incl_excluded:
  assumes "R' = M \<union> R" "M \<subseteq> N"
  shows "reach e N R' = reach e N R"
  proof -
    { fix p assume "p \<in> reach e N R'" hence "p \<in> reach e N R"
      using assms by (induction rule: reach.induct) auto }
    moreover
    { fix p assume "p \<in> reach e N R" hence "p \<in> reach e N R'"
      using assms by (induction rule: reach.induct) auto }
    ultimately
    show ?thesis using assms by blast
  qed

lemmas reach_incl_null
  = reach_incl_excluded[where M="{NULL}" and N="{NULL}", simplified]

lemma reach_rotate:
  assumes
    P: "p \<noteq> NULL" and
    R: "R = {s[p]\<rightarrow>left, p}"
  shows
    "reach_p s[p\<rightarrow>left := s[p]\<rightarrow>right][p\<rightarrow>right := q] R = reach_p s {p,q}"
  proof -
    {
      fix r
      assume "r \<in> reach_p s[p\<rightarrow>left := s[p]\<rightarrow>right][p\<rightarrow>right := q] {s[p]\<rightarrow>left, p}"
      hence "r \<in> reach_p s {p,q}"
      proof (induction rule: reach.induct)
        case reach_root thus ?case using assms out_def by blast
      next
        case reach_step thus ?case
        by (metis fun_upd_other fun_upd_same graph_mark.heap_abs_simps(12,14,22,24)
                  out_def reach.intros insertCI insertE)
      qed
    }
    moreover
    {
      fix r
      assume "r \<in> reach_p s {p,q}"
      hence "r \<in> reach_p s[p\<rightarrow>left := s[p]\<rightarrow>right][p\<rightarrow>right := q] {s[p]\<rightarrow>left, p}"
      proof (induction rule: reach.induct)
        case (reach_root r') show ?case
        proof (cases "r' = p")
          case True show ?thesis
          using reach_root True by auto
        next
          case False
          have Q: "r' = q" "q \<noteq> NULL" using False reach_root by auto
          show ?thesis
          by (rule reach_step[of p]) (auto simp: Q P out_def fun_upd_same)
        qed
      next
        case reach_step show ?case using reach_step P
        by (metis fun_upd_other fun_upd_same graph_mark.heap_abs_simps(12,14,22,24)
                  out_def empty_iff insertE insert_subset order_refl reach.intros)
      qed
    }
    ultimately show ?thesis using R by blast
  qed

lemma reach_rotate_left [simp]:
  "p \<noteq> NULL \<Longrightarrow> reach_p s[p\<rightarrow>left := s[p]\<rightarrow>right][p\<rightarrow>right := q] {s[p]\<rightarrow>left,p} = reach_p s {p,q}"
  "p \<noteq> NULL \<Longrightarrow> reach_p s[p\<rightarrow>left := s[p]\<rightarrow>right][p\<rightarrow>right := q] {p,s[p]\<rightarrow>left} = reach_p s {p,q}"
  by (rule reach_rotate; auto)+

lemma reach_rotate_id [simp]:
  assumes "s[p]\<rightarrow>left = p" "p \<noteq> NULL"
  shows "reach_p s[p\<rightarrow>left := s[p]\<rightarrow>right][p\<rightarrow>right := q] {p} = reach_p s {p,q}"
  by (rule reach_rotate) (auto simp: assms)

lemma reach_rotate_null [simp]:
  assumes
    "p \<noteq> NULL" "s[p]\<rightarrow>left = NULL"
  shows
    "reach_p s[p\<rightarrow>left := s[p]\<rightarrow>right][p\<rightarrow>right := q] {p,NULL} = reach_p s {p,q}"
    "reach_p s[p\<rightarrow>left := s[p]\<rightarrow>right][p\<rightarrow>right := q] {NULL,p} = reach_p s {p,q}"
  by (rule reach_rotate; auto simp: assms)+

lemma setsum_extract_reach:
  "p \<noteq> NULL \<Longrightarrow> (\<Sum> p \<in> reach_p s {p,q}. f p) = f p + (\<Sum> p \<in> reach_p s {p,q} - {p}. f p)"
  by (auto simp: reach_root setsum.remove)

lemma reach_left:
  "s[p]\<rightarrow>left \<noteq> NULL \<Longrightarrow> p \<noteq> NULL \<Longrightarrow> s[p]\<rightarrow>left \<in> reach_p s {p,q}"
  using out_def insertCI singletonD by auto

definition heaps_differ_at :: "lifted_globals \<Rightarrow> lifted_globals \<Rightarrow> node_C ptr set \<Rightarrow> bool" where
  "heaps_differ_at s t U \<equiv> \<exists> f. t = heap_node_C_update (\<lambda>h p. if p \<in> U then f p else h p) s"

primrec compare_links :: "lifted_globals \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr \<times> node_C ptr \<Rightarrow> bool" where
  "compare_links m p (l,r) = (l = m[p]\<rightarrow>left \<and> r = m[p]\<rightarrow>right)"

abbreviation links_same_at :: "lifted_globals \<Rightarrow> lifted_globals \<Rightarrow> node_C ptr \<Rightarrow> bool" where
  "links_same_at s t p \<equiv> compare_links t p (s[p]\<rightarrow>left, s[p]\<rightarrow>right)"

primrec
  path_ok :: "bool \<Rightarrow> lifted_globals \<Rightarrow> lifted_globals \<Rightarrow> node_C ptr set
    \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr list \<Rightarrow> bool"
where
  "path_ok z s t N r q p []        = (p = NULL \<and> q = r \<and> (z \<longrightarrow> r \<in> N))" |
  "path_ok z s t N r q p (p' # ps) = (p = p' \<and>
     (s[p]\<rightarrow>mark = 0 \<and> z \<and>
        compare_links t p (s[p]\<rightarrow>left, s[p]\<rightarrow>right) \<and>
        path_ok False s t N r p q ps \<or>
      s[p]\<rightarrow>mark = 1 \<and> (z \<longrightarrow> q \<in> N) \<and>
        compare_links t p (q, s[p]\<rightarrow>left) \<and>
        path_ok False s t N r p s[p]\<rightarrow>right ps \<or>
      s[p]\<rightarrow>mark = 2 \<and> (z \<longrightarrow> q \<in> N) \<and> t[p]\<rightarrow>left \<in> N \<and>
        compare_links t p (s[p]\<rightarrow>right, q) \<and>
        path_ok False s t N r p s[p]\<rightarrow>left ps))"

primrec mark_invariant :: "state_pred \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr \<times> node_C ptr \<Rightarrow> state_pred" where
  "mark_invariant P root (p,q) s =
    (\<exists> t path F.
      let
        R = reach_p t {root};
        M = set path \<union> F;
        N = insert NULL M;
        U = R - F;
        Z = R - M
      in
        P t \<and>
        heaps_differ_at s t U \<and>
        set path \<subseteq> R \<and>
        NULL \<notin> set path \<and>
        distinct path \<and>
        F \<subseteq> R \<and>
        reach (out t) (set (NULL # path)) F = F \<and>
        set path \<inter> F = {} \<and>
        R = reach_p s {p,q} \<and>
        path_ok True s t N root q p path \<and>
        (\<forall> p \<in> Z. s[p]\<rightarrow>mark = 0 \<and> links_same_at s t p) \<and>
        (\<forall> p \<in> R. t[p]\<rightarrow>mark = 3 \<and> is_valid_node_C s p))"

fun mark_measure :: "(node_C ptr \<times> node_C ptr) \<times> lifted_globals \<Rightarrow> nat" where
  "mark_measure ((p,q),s) = setsum (\<lambda> p. 3 - unat s[p]\<rightarrow>mark) (reach_p s {p,q})"

lemma heap_node_C_update_id [simp]: "heap_node_C_update id s = s"
  by simp

lemma heap_node_C_update_cong:
  "f (heap_node_C s) = g (heap_node_C s) \<Longrightarrow> heap_node_C_update f s = heap_node_C_update g s"
  by simp

lemmas heap_node_C_update_same [simp] = heap_node_C_update_cong[where g=id, simplified]

lemma mark_C_update_id [simp]: "mark_C_update id n = n"
  by (metis id_apply mark_C_update_def node_C.exhaust)

lemma mark_C_update_cong:
  "f (mark_C n) = g (mark_C n) \<Longrightarrow> mark_C_update f n = mark_C_update g n"
  by (metis mark_C_def mark_C_update_def node_C.exhaust)

lemmas mark_C_update_same [simp] = mark_C_update_cong[where g=id, simplified]

lemma mark_set_same:
  assumes "P \<subseteq> F" "\<forall> p \<in> F. s[p]\<rightarrow>mark = m"
  shows "mark_set m P s = s"
  unfolding mark_set_def
  apply (rule heap_node_C_update_same)
  apply (rule ext)
  apply (rule mark_C_update_same)
  apply (insert assms)
  by (auto simp: graph_mark.get_node_mark_def)

lemmas mark_set_empty [simp] = mark_set_same[of "{}" "{}", simplified]

lemma mark_set_get [elim]:
  "p \<in> R \<Longrightarrow> (mark_set m R s)[p]\<rightarrow>mark = m"
  by (simp add: mark_set_def graph_mark.get_node_mark_def)

lemma reach_decompose:
  "reach e N R = reach e N (E \<inter> reach e N R) \<union> reach e (E \<union> N) R"
  proof -
    {
      fix p assume "p \<in> reach e N R"
      hence "p \<in> reach e N (E \<inter> reach e N R) \<union> reach e (E \<union> N) R"
      proof (induction rule: reach.induct)
        case (reach_root p') thus ?case by (cases "p' \<in> E") auto
      next
        case reach_step thus ?case by blast
      qed
    }
    moreover
    {
      fix p assume "p \<in> reach e N (E \<inter> reach e N R)"
      hence "p \<in> reach e N R" by (induction rule: reach.induct) auto
    }
    moreover
    {
      fix p assume "p \<in> reach e (E \<union> N) R"
      hence "p \<in> reach e N R" by (induction rule: reach.induct) auto
    }
    ultimately show ?thesis by blast
  qed

lemma reach_closure_extend:
  assumes
    "reach e (E \<union> N) R = R"
    "\<forall> r \<in> E. e r \<subseteq> E \<union> N \<union> R"
    "E \<inter> N = {}"
  shows
    "reach e N (E \<union> R) = E \<union> R"
  proof -
    { fix p assume "p \<in> reach e N (E \<union> R)" hence "p \<in> E \<union> R"
      proof (induction rule: reach.induct)
        case reach_root thus ?case by blast
      next
        case (reach_step p' q') thus ?case using assms(1,2)
        by (metis (full_types) Un_iff contra_subsetD reach.reach_step)
      qed }
    moreover
    { fix p assume "p \<in> E \<union> R" hence "p \<in> reach e N (E \<union> R)"
      by (metis Un_iff assms(1,3) orthD1 reach.cases reach_root) }
    ultimately show ?thesis by blast
  qed

lemmas reach_closure_extend_p = reach_closure_extend
  [where E="{p}" and N="insert NULL ps" for p ps, simplified]

lemma heap_node_C_update_compose:
  "heap_node_C_update f (heap_node_C_update g s) = heap_node_C_update (\<lambda> h. f (g h)) s"
  by simp

lemma heaps_differ_at_alt:
  "heaps_differ_at s t U \<equiv> t = heap_node_C_update (\<lambda>h p. if p \<in> U then heap_node_C t p else h p) s"
  unfolding heaps_differ_at_def atomize_eq
  proof
    assume "\<exists>f. t = heap_node_C_update (\<lambda>h p. if p \<in> U then f p else h p) s"
    then obtain f where
      H: "t = heap_node_C_update (\<lambda> h p. if p \<in> U then f p else h p) s"
      by blast
    show "t = heap_node_C_update (\<lambda>h p. if p \<in> U then heap_node_C t p else h p) s"
      apply (subst H)
      apply (rule heap_node_C_update_cong, rule ext)
      by (clarsimp simp: H)
  next
    assume "t = heap_node_C_update (\<lambda>h p. if p \<in> U then heap_node_C t p else h p) s"
    thus "\<exists>f. t = heap_node_C_update (\<lambda>h p. if p \<in> U then f p else h p) s"
      by blast
  qed

lemma heaps_differ_at_id: "heaps_differ_at t t U"
  unfolding heaps_differ_at_def
  apply (rule exI[of _ "heap_node_C t"])
  by simp

lemma wtf_no_no_no: "(if c then t else if c then n else f) = (if c then t else f)"
  by simp

lemma heaps_differ_at_sym_imp:
  assumes "heaps_differ_at t s U"
  shows "heaps_differ_at s t U"
  proof -
    obtain f where
      H: "s = heap_node_C_update (\<lambda> h p. if p \<in> U then f p else h p) t"
      using assms(1) by (simp add: heaps_differ_at_def) blast
    show ?thesis
      apply (unfold heaps_differ_at_def)
      apply (rule exI[of _ "heap_node_C t"])
      apply (subst H)
      apply (subst heap_node_C_update_compose)
      apply (subst wtf_no_no_no)
      by simp
  qed

lemma heaps_differ_at_p:
  assumes
    "p \<in> U"
    "heaps_differ_at s t U"
  shows
    "heaps_differ_at (heap_node_C_update (\<lambda> h. h (p := f h)) s) t U" (is ?r0)
    "heaps_differ_at (mark_incr p s)  t U" (is ?r1)
    "heaps_differ_at s[p\<rightarrow>left  := l] t U" (is ?r2)
    "heaps_differ_at s[p\<rightarrow>right := r] t U" (is ?r3)
  proof -
    obtain f where
      H: "t = heap_node_C_update (\<lambda> h p. if p \<in> U then f p else h p) s"
      using assms(2) by (simp add: heaps_differ_at_def) blast
    show ?r0 ?r1 ?r2 ?r3
    unfolding
      H heaps_differ_at_def mark_incr_def heap_node_C_update_compose
      graph_mark.update_node_left_def graph_mark.update_node_right_def
    by (rule exI[of _ f]; rule heap_node_C_update_cong; rule ext;
        simp add: assms(1) fun_upd_def)+
  qed

lemma node_eq_elements:
  "heap_node_C s p = heap_node_C t p
    \<longleftrightarrow> s[p]\<rightarrow>left = t[p]\<rightarrow>left \<and> s[p]\<rightarrow>right = t[p]\<rightarrow>right \<and> s[p]\<rightarrow>mark = t[p]\<rightarrow>mark"
  by (metis graph_mark.get_node_left_def graph_mark.get_node_mark_def
            graph_mark.get_node_right_def node_C_idupdates(1))

lemma heaps_differ_at_replace:
  assumes
    "heaps_differ_at u s V"
    "\<forall> p \<in> V. heap_node_C t p = heap_node_C u p"
  shows
    "u = heap_node_C_update (\<lambda> h p. if p \<in> V then heap_node_C t p else h p) s"
  apply (subst heaps_differ_at_sym_imp[OF assms(1), simplified heaps_differ_at_alt])
  apply (rule heap_node_C_update_cong, rule ext)
  by (simp add: assms(2))

lemma heaps_differ_at_shrink':
  assumes
    "heaps_differ_at s t U"
    "u = heap_node_C_update (\<lambda> h p. if p \<in> V then heap_node_C t p else h p) s"
    "V \<subseteq> U"
    "R = U - V"
  shows
    "heaps_differ_at u t R"
  proof -
    have F: "t = heap_node_C_update (\<lambda> h p. if p \<in> U then heap_node_C t p else h p) s"
      using assms(1) heaps_differ_at_alt by simp
    show ?thesis
      unfolding heaps_differ_at_def assms(4)
      apply (subst F)
      apply (subst assms(2))
      apply (subst heap_node_C_update_compose)
      apply (rule exI[of _ "heap_node_C t"])
      apply (rule heap_node_C_update_cong, rule ext)
      using assms(3) by simp blast
  qed

lemmas heaps_differ_at_shrink
  = heaps_differ_at_shrink'[OF _ heaps_differ_at_replace]

lemma path_ok_upd_other:
  assumes
    "n \<notin> set ps"
    "path_ok z s t N root q p ps"
  shows
    "path_ok z (mark_incr n s) t N root q p ps"
    "path_ok z (s[n\<rightarrow>left := l]) t N root q p ps"
    "path_ok z (s[n\<rightarrow>right := r]) t N root q p ps"
  using assms
  by (induction ps arbitrary: p q z; clarsimp;
      elim disjE; clarsimp simp: fun_upd_def)+

lemma path_ok_imp:
  assumes "q \<in> N" "path_ok False s t N root q p ps"
  shows "path_ok True s t N root q p ps"
  using assms by (cases ps; clarsimp)

method rotate_p for path :: "node_C ptr list" and F :: "node_C ptr set" =
  (rule exI[of _ path]; rule exI[of _ F];
   clarsimp simp: fun_upd_def heaps_differ_at_p path_ok_upd_other;
   rule ccontr; clarsimp)

method step_back for ps :: "node_C ptr list" and p :: "node_C ptr" and F :: "node_C ptr set" =
  (rule exI[of _ ps]; rule exI[of _ "insert p F"];
   ((frule reach_closure_extend_p; clarsimp simp: fun_upd_def), fastforce simp: out_def);
   clarsimp simp: path_ok_upd_other path_ok_imp;
   erule heaps_differ_at_shrink[where V="{p}", simplified node_eq_elements];
   (rule Diff_insert | clarsimp simp: heaps_differ_at_id heaps_differ_at_p fun_upd_def))

lemma path_False_mark_non_zero: "path_ok False s t N r q p ps \<Longrightarrow> s[n]\<rightarrow>mark = 0 \<Longrightarrow> n \<notin> set ps"
  by (induction ps arbitrary: q p) auto

lemma heaps_differ_at:
  "heaps_differ_at s t U \<Longrightarrow> heap_node_C s p \<noteq> heap_node_C t p \<Longrightarrow> p \<in> U"
  by (cases "p \<in> U"; clarsimp simp: heaps_differ_at_def)

lemma reach_exclude: "reach e N R = S \<Longrightarrow> P \<inter> S = {} \<Longrightarrow> N' = P \<union> N \<Longrightarrow> reach e N' R = S"
  by (metis Un_empty_left reach_decompose reachable_excluded_simps(1))

lemmas reach_exclude_one = reach_exclude[where P="{p}" for p, simplified]

lemma path_ok_extend: "path_ok z s t N r q p ps \<Longrightarrow> N \<subseteq> M \<Longrightarrow> path_ok z s t M r q p ps"
  by (induction ps arbitrary: z q p) auto

method try_solve methods m = (m; fail)?

method step_forward for left :: "node_C ptr" and path :: "node_C ptr list" and F :: "node_C ptr set" =
  (rule exI[of _ "left # path"]; rule exI[of _ F];
   clarsimp simp: fun_upd_def heaps_differ_at_p path_False_mark_non_zero;
   frule heaps_differ_at[where p=left]; clarsimp simp: node_eq_elements;
   frule bspec[of _ _ left]; clarsimp simp: path_False_mark_non_zero;
   intro conjI; try_solve \<open>clarsimp simp: reach_exclude_one[OF _ _ insert_commute]\<close>;
   (rule path_ok_upd_other, clarsimp simp: path_False_mark_non_zero)+;
   elim path_ok_extend; blast)

theorem graph_mark'_correct: "mark_specification P root"
  unfolding mark_specification_def mark_precondition_def graph_mark'_def
  unfolding mark_incr_def[symmetric]
  unfolding whileLoop_add_inv[where I="mark_invariant P root" and M="mark_measure"]
  apply (wp; clarsimp simp: mark_incr_ptr_upd)
  subgoal for p q s t path F
   apply (cases path; clarsimp simp: Let_def)
   subgoal for ps
    apply (subst setsum_extract_reach[of p], assumption)+
    apply (cases "s[p]\<rightarrow>left = p";
           cases "s[p]\<rightarrow>left = NULL";
           (frule (1) reach_left[where q=q])?;
           cases "s[s[p]\<rightarrow>left]\<rightarrow>mark = 0";
           elim disjE; clarsimp;
           rule exI[of _ t]; clarsimp)
     subgoal by (rotate_p path F)
     subgoal by (rotate_p path F)
     subgoal by (cases ps; clarsimp)
     subgoal by (rotate_p path F)
     subgoal by (rotate_p path F)
     subgoal by (step_back ps p F)
     subgoal by (rotate_p path F)
     subgoal by (rotate_p path F)
     subgoal by (step_back ps p F)
     subgoal by (step_forward "t[p]\<rightarrow>left" path F)
     subgoal by (step_forward "t[p]\<rightarrow>right" path F)
     subgoal by (step_back ps p F)
     subgoal by (rotate_p path F)
     subgoal by (rotate_p path F)
     subgoal by (step_back ps p F)
    done
   done
  subgoal for q s t path F
   apply (cases path; cases "root = NULL"; clarsimp simp: Let_def heaps_differ_at_def)
   apply (frule reach_subset[of "{root}" F "out t" "{NULL}", simplified])
   by auto
  subgoal for s
   apply (rule exI[of _ "mark_set 3 (reach (out s) {NULL} {root}) s"];
          rule exI[of _ "if root = NULL then [] else [root]"];
          rule exI[of _ "{}"])
   apply (auto simp: Let_def reach_incl_null[OF insert_commute] heaps_differ_at_def)
   apply (simp add: mark_set_def)
   apply (rule exI[of _ "mark_C_update (If True 3) \<circ> heap_node_C s"])
   apply (rule heap_node_C_update_cong, rule ext)
   by clarsimp
  done

end

end
