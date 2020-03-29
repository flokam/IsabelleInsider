section \<open>Airplane case study\<close>
theory Airplane
imports AirInsider
begin
datatype doorstate = locked | norm | unlocked
datatype position = air | airport | ground

locale airplane =

fixes airplane_actors :: "identity set"
defines airplane_actors_def: "airplane_actors \<equiv> {''Bob'', ''Charly'', ''Alice''}"

fixes airplane_locations :: "location set"
defines airplane_locations_def: 
"airplane_locations \<equiv> {Location 0, Location 1, Location 2}"
(* 0 cabin, 1 door, 2 cockpit *)
fixes cockpit :: "location"
defines cockpit_def: "cockpit \<equiv> Location 2" 
fixes door :: "location"
defines door_def: "door \<equiv> Location 1" 
fixes cabin :: "location"
defines cabin_def: "cabin \<equiv> Location 0" 

fixes global_policy :: "[infrastructure, identity] \<Rightarrow> bool"
defines global_policy_def: "global_policy I a \<equiv> a \<notin> airplane_actors 
                 \<longrightarrow> \<not>(enables I cockpit (Actor a) put)"

fixes ex_creds :: "actor  \<Rightarrow> (string list * string list)"
defines ex_creds_def: "ex_creds \<equiv> 
        (\<lambda> x.(if x = Actor ''Bob'' 
              then ([''PIN''], [''pilot''])        
              else (if x = Actor ''Charly'' 
                    then ([''PIN''],[''copilot''])
                    else (if x = Actor ''Alice''  
                          then ([''PIN''],[''flightattendant''])
                                else ([],[])))))"

fixes ex_locs :: "location \<Rightarrow> string list"
defines ex_locs_def: "ex_locs \<equiv>  (\<lambda> x. if x = door then [''norm''] else 
                                       (if x = cockpit then [''air''] else []))"
  
fixes ex_locs' :: "location \<Rightarrow> string list"
defines ex_locs'_def: "ex_locs' \<equiv>  (\<lambda> x. if x = door then [''locked''] else
                                         (if x = cockpit then [''air''] else []))"
fixes ex_graph :: "igraph"
defines ex_graph_def: "ex_graph \<equiv> Lgraph
      {(cockpit, door),(door,cabin)}
      (\<lambda> x. if x = cockpit then [''Bob'', ''Charly''] 
            else (if x = door then [] 
                  else (if x = cabin then [''Alice''] else [])))
      ex_creds ex_locs"

fixes aid_graph :: "igraph"
defines aid_graph_def: "aid_graph \<equiv>  Lgraph
      {(cockpit, door),(door,cabin)}
      (\<lambda> x. if x = cockpit then [''Charly''] 
            else (if x = door then [] 
                  else (if x = cabin then [''Bob'', ''Alice''] else [])))
      ex_creds ex_locs'"
  
fixes aid_graph0 :: "igraph"
defines aid_graph0_def: "aid_graph0 \<equiv>  Lgraph
      {(cockpit, door),(door,cabin)}
      (\<lambda> x. if x = cockpit then [''Charly''] 
            else (if x = door then [''Bob''] 
                  else (if x = cabin then [''Alice''] else [])))
        ex_creds ex_locs"

fixes agid_graph :: "igraph"
defines agid_graph_def: "agid_graph \<equiv>  Lgraph
      {(cockpit, door),(door,cabin)}
      (\<lambda> x. if x = cockpit then [''Charly''] 
            else (if x = door then [] 
                  else (if x = cabin then [''Bob'', ''Alice''] else [])))
      ex_creds ex_locs"
  
fixes local_policies :: "[igraph,  location] \<Rightarrow> policy set"
defines local_policies_def: "local_policies G \<equiv>  
   (\<lambda> y. if y = cockpit then
             {(\<lambda> x. (? n. (n @\<^bsub>G\<^esub> cockpit) \<and> Actor n = x), {put}),
              (\<lambda> x. (? n. (n @\<^bsub>G\<^esub> cabin) \<and> Actor n = x \<and> has G (x, ''PIN'')
                    \<and> isin G door ''norm''),{move})
             }
         else (if y = door then {(\<lambda> x. True, {move}),
                       (\<lambda> x. (? n. (n @\<^bsub>G\<^esub> cockpit) \<and> Actor n = x), {put})}
               else (if y = cabin then {(\<lambda> x. True, {move})} 
                     else {})))"

(* changed policy in which always two have to be in cockpit to do a put,
   simply change the above to two actors *)
fixes local_policies_four_eyes :: "[igraph, location] \<Rightarrow> policy set"
defines local_policies_four_eyes_def: "local_policies_four_eyes G \<equiv>  
   (\<lambda> y. if y = cockpit then
             {(\<lambda> x.  (? n. (n @\<^bsub>G\<^esub> cockpit) \<and> Actor n = x) \<and>
                     2 \<le> length(agra G y) \<and> (\<forall> h \<in> set(agra G y). h \<in> airplane_actors), {put}),
              (\<lambda> x. (? n. (n @\<^bsub>G\<^esub> cabin) \<and> Actor n = x \<and> has G (x, ''PIN'') \<and> 
                           isin G door ''norm'' ),{move})
             }
         else (if y = door then 
              {(\<lambda> x.  ((? n. (n @\<^bsub>G\<^esub> cockpit) \<and> Actor n = x) \<and> 3 \<le> length(agra G cockpit)), {move})}
               else (if y = cabin then 
                     {(\<lambda> x. ((? n. (n @\<^bsub>G\<^esub> door) \<and> Actor n = x)), {move})} 
                           else {})))"

fixes Airplane_scenario :: "infrastructure" (structure)
defines Airplane_scenario_def:
"Airplane_scenario \<equiv> Infrastructure ex_graph local_policies"

fixes Airplane_in_danger :: "infrastructure"
defines Airplane_in_danger_def:
"Airplane_in_danger \<equiv> Infrastructure aid_graph local_policies"

(* Intermediate step where pilot left cockpit but door still in
   norm position *)
fixes Airplane_getting_in_danger0 :: "infrastructure"
defines Airplane_getting_in_danger0_def:
"Airplane_getting_in_danger0 \<equiv> Infrastructure aid_graph0 local_policies"

fixes Airplane_getting_in_danger :: "infrastructure"
defines Airplane_getting_in_danger_def:
"Airplane_getting_in_danger \<equiv> Infrastructure agid_graph local_policies"

(* For state transition we need Kripke structure *)
fixes Air_states
defines Air_states_def: "Air_states \<equiv> { I. Airplane_scenario \<rightarrow>\<^sub>n* I }"

fixes Air_Kripke
defines "Air_Kripke \<equiv> Kripke Air_states {Airplane_scenario}"

(* Two-person policy excludes attack *)
fixes Airplane_not_in_danger :: "infrastructure"
defines Airplane_not_in_danger_def:
"Airplane_not_in_danger \<equiv> Infrastructure aid_graph local_policies_four_eyes"

fixes Airplane_not_in_danger_init :: "infrastructure"
defines Airplane_not_in_danger_init_def:
"Airplane_not_in_danger_init \<equiv> Infrastructure ex_graph local_policies_four_eyes"

(* Kripke for two-person variant*)
fixes Air_tp_states
defines Air_tp_states_def: "Air_tp_states \<equiv> { I. Airplane_not_in_danger_init \<rightarrow>\<^sub>n* I }"

fixes Air_tp_Kripke
defines "Air_tp_Kripke \<equiv> Kripke Air_tp_states {Airplane_not_in_danger_init}"

(* Safety *)
fixes Safety :: "[infrastructure, identity] \<Rightarrow> bool"
defines Safety_def: "Safety I a \<equiv> a \<in> airplane_actors  
                       \<longrightarrow> (enables I cockpit (Actor a) move)"
(* Security *)
fixes Security :: "[infrastructure, identity] \<Rightarrow> bool"
defines Security_def: "Security I a \<equiv>  (isin (graphI I) door ''locked'') 
                       \<longrightarrow> \<not>(enables I cockpit (Actor a) move)"

fixes foe_control :: "[location, action] \<Rightarrow> bool"
defines foe_control_def: "foe_control l c \<equiv>  
   (! I:: infrastructure. (? x :: identity. 
        x @\<^bsub>graphI I\<^esub> l \<and> Actor x \<noteq> Actor ''Eve'')
             \<longrightarrow> \<not>(enables I l (Actor ''Eve'') c))"

fixes astate:: "identity \<Rightarrow> actor_state"
defines astate_def: "astate x \<equiv>  (case x of 
           ''Eve'' \<Rightarrow> Actor_state depressed {revenge, peer_recognition}
          | _ \<Rightarrow> Actor_state happy {})"

assumes Eve_precipitating_event: "tipping_point (astate ''Eve'')"
assumes Insider_Eve: "Insider ''Eve'' {''Charly''} astate"
assumes cockpit_foe_control: "foe_control cockpit put"

begin

lemma ex_inv: "global_policy Airplane_scenario ''Bob''"
by (simp add: Airplane_scenario_def global_policy_def airplane_actors_def)

lemma ex_inv2: "global_policy Airplane_scenario ''Charly''"
by (simp add: Airplane_scenario_def global_policy_def airplane_actors_def)

lemma ex_inv3: "\<not>global_policy Airplane_scenario ''Eve''"
proof (simp add: Airplane_scenario_def global_policy_def, rule conjI)
  show "''Eve'' \<notin> airplane_actors" by (simp add: airplane_actors_def)
next show 
  "enables (Infrastructure ex_graph local_policies) cockpit (Actor ''Eve'') put"
  proof -
    have a: "Actor ''Charly'' = Actor ''Eve''" 
      by (insert Insider_Eve, unfold Insider_def, (drule mp), 
          rule Eve_precipitating_event, simp add: UasI_def)
    show ?thesis   
      by (insert a, simp add: Airplane_scenario_def enables_def ex_creds_def local_policies_def ex_graph_def,
         insert Insider_Eve, unfold Insider_def, (drule mp), rule Eve_precipitating_event, 
         simp add: UasI_def, rule_tac x = "''Charly''" in exI, simp add: cockpit_def atI_def)
  qed
qed

text\<open>show Safety for Airplane\_scenario\<close> 
lemma Safety: "Safety Airplane_scenario (''Alice'')"
proof -
  show "Safety Airplane_scenario ''Alice''"
    by (simp add: Airplane_scenario_def Safety_def enables_def ex_creds_def 
                local_policies_def ex_graph_def cockpit_def, rule impI,
        rule_tac x = "''Alice''" in exI, simp add: atI_def cabin_def ex_locs_def door_def,
        rule conjI, simp add: has_def credentials_def, simp add: isin_def credentials_def)
qed

text \<open>show Security for Airplane\_scenario\<close>
lemma inj_lem: "\<lbrakk> inj f; x \<noteq> y \<rbrakk> \<Longrightarrow> f x \<noteq> f y"
by (simp add: inj_eq)

lemma inj_on_lem: "\<lbrakk> inj_on f A; x \<noteq> y; x\<in> A; y \<in> A \<rbrakk> \<Longrightarrow> f x \<noteq> f y"
by (simp add: inj_on_def, blast)

lemma inj_lemma': "inj_on (isin ex_graph door) {''locked'',''norm''} "
  by (unfold inj_on_def ex_graph_def isin_def, simp, unfold ex_locs_def, simp)

lemma inj_lemma'': "inj_on (isin aid_graph door) {''locked'',''norm''} "
 by (unfold inj_on_def aid_graph_def isin_def, simp, unfold ex_locs'_def, simp)

lemma locl_lemma2: "isin ex_graph door ''norm'' \<noteq> isin ex_graph door ''locked''"
by (rule_tac A = "{''locked'',''norm''}" and f = "isin ex_graph door" in inj_on_lem,
        rule inj_lemma', simp+)

lemma locl_lemma3: "isin ex_graph door ''norm'' = (\<not> isin ex_graph door ''locked'')"
by (insert locl_lemma2, blast)

lemma locl_lemma2a: "isin aid_graph door ''norm'' \<noteq> isin aid_graph door ''locked''"
by (rule_tac A = "{''locked'',''norm''}" and f = "isin aid_graph door" in inj_on_lem,
       rule inj_lemma'', simp+)

lemma locl_lemma3a: "isin aid_graph door ''norm'' = (\<not> isin aid_graph door ''locked'')"
by (insert locl_lemma2a, blast)

lemma Security: "Security Airplane_scenario s"
  by (simp add: Airplane_scenario_def Security_def enables_def local_policies_def ex_locs_def locl_lemma3)
 
text \<open>show that pilot can't get into cockpit if outside and locked = Airplane\_in\_danger\<close>
lemma Security_problem: "Security Airplane_scenario ''Bob''"
by (rule Security)

text \<open>show that pilot can get out of cockpit\<close>
lemma pilot_can_leave_cockpit: "(enables Airplane_scenario cabin (Actor ''Bob'') move)"
  by (simp add: Airplane_scenario_def Security_def ex_creds_def ex_graph_def enables_def 
                local_policies_def ex_locs_def, simp add: cockpit_def cabin_def door_def)

text \<open>show that in Airplane\_in\_danger copilot can still do put = put position to ground\<close>
lemma ex_inv4: "\<not>global_policy Airplane_in_danger (''Eve'')"
proof (simp add: Airplane_in_danger_def global_policy_def, rule conjI)
  show "''Eve'' \<notin> airplane_actors" by (simp add: airplane_actors_def)
next show "enables (Infrastructure aid_graph local_policies) cockpit (Actor ''Eve'') put"
  proof -
    have a: "Actor ''Charly'' = Actor ''Eve''" 
      by (insert Insider_Eve, unfold Insider_def, (drule mp), 
          rule Eve_precipitating_event, simp add: UasI_def)
    show ?thesis
     apply (insert a, erule subst)
     by (simp add: enables_def local_policies_def cockpit_def aid_graph_def atI_def)
 qed
qed

lemma Safety_in_danger:
  fixes s
  assumes "s \<in> airplane_actors" 
  shows   "\<not>(Safety Airplane_in_danger s)"
proof (simp add: Airplane_in_danger_def Safety_def enables_def assms)
  show "\<forall>x::(actor \<Rightarrow> bool) \<times> action set\<in>local_policies aid_graph cockpit.
       \<not> (case x of (p::actor \<Rightarrow> bool, e::action set) \<Rightarrow> move \<in> e \<and> p (Actor s))"
    by ( simp add: local_policies_def aid_graph_def ex_locs'_def isin_def)
qed

lemma Security_problem': " \<not>(enables Airplane_in_danger cockpit (Actor ''Bob'') move) "
proof (simp add: Airplane_in_danger_def Security_def enables_def local_policies_def 
       ex_locs_def locl_lemma3a, rule impI)
  assume "has aid_graph (Actor ''Bob'', ''PIN'')"
  show "(\<forall>n::char list.
        Actor n = Actor ''Bob'' \<longrightarrow> n @\<^bsub>aid_graph\<^esub> cabin \<longrightarrow> isin aid_graph door ''locked'')"
by (simp add: aid_graph_def isin_def ex_locs'_def)
qed

text \<open>show that with the four eyes rule in Airplane\_not\_in\_danger Eve cannot 
   crash plane, i.e. cannot put position to ground\<close>
lemma ex_inv5: "a \<in> airplane_actors \<longrightarrow> global_policy Airplane_not_in_danger a"
by (simp add: Airplane_not_in_danger_def global_policy_def)

lemma ex_inv6: "global_policy Airplane_not_in_danger a"
proof (simp add: Airplane_not_in_danger_def global_policy_def, rule impI)
  assume "a \<notin> airplane_actors"
  show "\<not> enables (Infrastructure aid_graph local_policies_four_eyes) cockpit (Actor a) put"
by (simp add: aid_graph_def ex_locs'_def enables_def local_policies_four_eyes_def)
qed
   
lemma step0:  "Airplane_scenario \<rightarrow>\<^sub>n Airplane_getting_in_danger0"
proof (rule_tac l = cockpit and l' = door and a = "''Bob''" in  move, rule refl)
  show "''Bob'' @\<^bsub>graphI Airplane_scenario\<^esub> cockpit"
  by (simp add: Airplane_scenario_def atI_def ex_graph_def)
next show "cockpit \<in> nodes (graphI Airplane_scenario)"
    by (simp add: ex_graph_def Airplane_scenario_def nodes_def, blast)+
next show "door \<in> nodes (graphI Airplane_scenario)"
   by (simp add: actors_graph_def door_def cockpit_def nodes_def cabin_def,
       rule_tac x = "Location 2" in exI,     
       simp add: Airplane_scenario_def ex_graph_def cockpit_def door_def)
next show "''Bob'' \<in> actors_graph (graphI Airplane_scenario)"
    by (simp add: actors_graph_def Airplane_scenario_def nodes_def ex_graph_def, blast)
next show "enables Airplane_scenario door (Actor ''Bob'') move"
   by (simp add: Airplane_scenario_def enables_def local_policies_def ex_creds_def door_def cockpit_def)
next show "Airplane_getting_in_danger0 =
    Infrastructure (move_graph_a ''Bob'' cockpit door (graphI Airplane_scenario))
     (delta Airplane_scenario)"
  proof -
    have a: "(move_graph_a ''Bob'' cockpit door (graphI Airplane_scenario)) = aid_graph0" 
      by (simp add: move_graph_a_def door_def cockpit_def Airplane_scenario_def 
          aid_graph0_def ex_graph_def, rule ext, simp add: cabin_def door_def)
    show ?thesis
      by (unfold Airplane_getting_in_danger0_def, insert a, erule ssubst, 
          simp add: Airplane_scenario_def)
  qed
qed
    
lemma step1:  "Airplane_getting_in_danger0 \<rightarrow>\<^sub>n Airplane_getting_in_danger"
proof (rule_tac l = door and l' = cabin and a = "''Bob''" in  move, rule refl)
  show "''Bob'' @\<^bsub>graphI Airplane_getting_in_danger0\<^esub> door"
  by (simp add: Airplane_getting_in_danger0_def atI_def aid_graph0_def door_def cockpit_def)
next show "door \<in> nodes (graphI Airplane_getting_in_danger0)"
    by (simp add: aid_graph0_def Airplane_getting_in_danger0_def nodes_def, blast)+
next show "cabin \<in> nodes (graphI Airplane_getting_in_danger0)"
    by (simp add: actors_graph_def door_def cockpit_def nodes_def cabin_def,
    rule_tac x = "Location 1" in exI,    
    simp add: Airplane_getting_in_danger0_def aid_graph0_def cockpit_def door_def cabin_def)
next show "''Bob'' \<in> actors_graph (graphI Airplane_getting_in_danger0)"
   by (simp add: actors_graph_def door_def cockpit_def nodes_def cabin_def 
                  Airplane_getting_in_danger0_def aid_graph0_def, blast)
next show "enables Airplane_getting_in_danger0 cabin (Actor ''Bob'') move"
   by (simp add: Airplane_getting_in_danger0_def enables_def local_policies_def ex_creds_def door_def 
                cockpit_def cabin_def)
next show "Airplane_getting_in_danger =
    Infrastructure (move_graph_a ''Bob'' door cabin (graphI Airplane_getting_in_danger0))
     (delta Airplane_getting_in_danger0)"
    by (unfold Airplane_getting_in_danger_def,
        simp add: Airplane_getting_in_danger0_def agid_graph_def aid_graph0_def 
                  move_graph_a_def door_def cockpit_def cabin_def, rule ext,
        simp add: cabin_def door_def)
qed

lemma step2: "Airplane_getting_in_danger \<rightarrow>\<^sub>n Airplane_in_danger"
proof (rule_tac l = door and a = "''Charly''" and z = "''locked''" in  put_remote, rule refl)
  show "enables Airplane_getting_in_danger door (Actor ''Charly'') put"
   by (simp add: enables_def local_policies_def ex_creds_def door_def cockpit_def,
       unfold Airplane_getting_in_danger_def,
       simp add: local_policies_def cockpit_def cabin_def door_def,
       rule_tac x = "''Charly''" in exI, rule conjI,
       simp add: atI_def agid_graph_def door_def cockpit_def, rule refl) 
next show "Airplane_in_danger =
    Infrastructure
     (Lgraph (gra (graphI Airplane_getting_in_danger)) (agra (graphI Airplane_getting_in_danger))
       (cgra (graphI Airplane_getting_in_danger))
       ((lgra (graphI Airplane_getting_in_danger))(door := [''locked''])))
     (delta Airplane_getting_in_danger)"
    by (unfold Airplane_in_danger_def, simp add: aid_graph_def agid_graph_def 
               ex_locs'_def ex_locs_def Airplane_getting_in_danger_def, force)
qed

lemma step0r: "Airplane_scenario \<rightarrow>\<^sub>n* Airplane_getting_in_danger0"
  by (simp add: state_transition_in_refl_def, insert step0, auto)

lemma step1r: "Airplane_getting_in_danger0 \<rightarrow>\<^sub>n* Airplane_getting_in_danger"
  by (simp add: state_transition_in_refl_def, insert step1, auto)

lemma step2r: "Airplane_getting_in_danger \<rightarrow>\<^sub>n* Airplane_in_danger"
  by (simp add: state_transition_in_refl_def, insert step2, auto)
  
theorem step_allr:  "Airplane_scenario \<rightarrow>\<^sub>n* Airplane_in_danger"
  by (insert step0r step1r step2r, simp add: state_transition_in_refl_def)

theorem aid_attack: "Air_Kripke \<turnstile> EF ({x. \<not> global_policy x ''Eve''})"
proof (simp add: check_def Air_Kripke_def, rule conjI)
  show "Airplane_scenario \<in> Air_states" 
    by (simp add: Air_states_def state_transition_in_refl_def)
next show "Airplane_scenario \<in> EF {x::infrastructure. \<not> global_policy x ''Eve''}"
  by (rule EF_lem2b, subst EF_lem000, rule EX_lem0r, subst EF_lem000, rule EX_step,
     unfold state_transition_infra_def, rule step0, rule EX_lem0r,
     rule_tac y = "Airplane_getting_in_danger" in EX_step,
     unfold state_transition_infra_def, rule step1, subst EF_lem000, rule EX_lem0l,
     rule_tac y = "Airplane_in_danger" in EX_step, unfold state_transition_infra_def,
     rule step2, rule CollectI, rule ex_inv4)
qed 
    
text \<open>Invariant: actors cannot be at two places at the same time\<close>
lemma  actors_unique_loc_base: 
  assumes "I \<rightarrow>\<^sub>n I'"
      and "(\<forall> l l'. a @\<^bsub>graphI I\<^esub> l \<and> a @\<^bsub>graphI I\<^esub> l' \<longrightarrow> l = l')\<and>
           (\<forall> l. nodup a (agra (graphI I) l))"
    shows "(\<forall> l l'. a @\<^bsub>graphI I'\<^esub> l \<and> a @\<^bsub>graphI I'\<^esub> l'  \<longrightarrow> l = l') \<and>
           (\<forall> l. nodup a (agra (graphI I') l))"
proof (rule state_transition_in.cases, rule assms(1))
  show "\<And>(G::igraph) (Ia::infrastructure) (aa::char list) (l::location) (a'::char list) (z::char list)
       I'a::infrastructure.
       I = Ia \<Longrightarrow>
       I' = I'a \<Longrightarrow>
       G = graphI Ia \<Longrightarrow>
       aa @\<^bsub>G\<^esub> l \<Longrightarrow>
       a' @\<^bsub>G\<^esub> l \<Longrightarrow>
       has G (Actor aa, z) \<Longrightarrow>
       enables Ia l (Actor aa) get \<Longrightarrow>
       I'a =
       Infrastructure
        (Lgraph (gra G) (agra G)
          ((cgra G)(Actor a' := (z # fst (cgra G (Actor a')), snd (cgra G (Actor a'))))) (lgra G))
        (delta Ia) \<Longrightarrow>
       (\<forall>(l::location) l'::location. a @\<^bsub>graphI I'\<^esub> l \<and> a @\<^bsub>graphI I'\<^esub> l' \<longrightarrow> l = l') \<and>
       (\<forall>l::location. nodup a (agra (graphI I') l))" using assms
    by (simp add: atI_def)
next fix G Ia aa l I'a z
  assume a0: "I = Ia" and a1: "I' = I'a" and a2: "G = graphI Ia" and a3: "aa @\<^bsub>G\<^esub> l"
     and a4: "enables Ia l (Actor aa) put" 
     and a5: "I'a = Infrastructure (Lgraph (gra G) (agra G) (cgra G) ((lgra G)(l := [z]))) (delta Ia)"
  show "(\<forall>(l::location) l'::location. a @\<^bsub>graphI I'\<^esub> l \<and> a @\<^bsub>graphI I'\<^esub> l' \<longrightarrow> l = l') \<and>
       (\<forall>l::location. nodup a (agra (graphI I') l))"using assms
    by (simp add: a0 a1 a2 a3 a4 a5 atI_def)
next show "\<And>(G::igraph) (Ia::infrastructure) (l::location) (aa::char list) (I'a::infrastructure)
       z::char list.
       I = Ia \<Longrightarrow>
       I' = I'a \<Longrightarrow>
       G = graphI Ia \<Longrightarrow>
       enables Ia l (Actor aa) put \<Longrightarrow>
       I'a = Infrastructure (Lgraph (gra G) (agra G) (cgra G) ((lgra G)(l := [z]))) (delta Ia) \<Longrightarrow>
       (\<forall>(l::location) l'::location. a @\<^bsub>graphI I'\<^esub> l \<and> a @\<^bsub>graphI I'\<^esub> l' \<longrightarrow> l = l') \<and>
       (\<forall>l::location. nodup a (agra (graphI I') l))"
    by (clarify, simp add: assms atI_def)
next show "\<And>(G::igraph) (Ia::infrastructure) (aa::char list) (l::location) (l'::location)
       I'a::infrastructure.
       I = Ia \<Longrightarrow>
       I' = I'a \<Longrightarrow>
       G = graphI Ia \<Longrightarrow>
       aa @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> nodes G \<Longrightarrow>
       l' \<in> nodes G \<Longrightarrow>
       aa \<in> actors_graph (graphI Ia) \<Longrightarrow>
       enables Ia l' (Actor aa) move \<Longrightarrow>
       I'a = Infrastructure (move_graph_a aa l l' (graphI Ia)) (delta Ia) \<Longrightarrow>
       (\<forall>(l::location) l'::location. a @\<^bsub>graphI I'\<^esub> l \<and> a @\<^bsub>graphI I'\<^esub> l' \<longrightarrow> l = l') \<and>
       (\<forall>l::location. nodup a (agra (graphI I') l))"
  proof (simp add: move_graph_a_def,rule conjI, clarify, rule conjI, clarify, rule conjI, clarify)
    show "\<And>(G::igraph) (Ia::infrastructure) (aa::char list) (l::location) (l'::location)
       (I'a::infrastructure) (la::location) l'a::location.
       I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor a) move \<Longrightarrow>
       a \<in> set (agra (graphI I) l) \<Longrightarrow>
       a \<notin> set (agra (graphI I) l') \<Longrightarrow>
       a @\<^bsub>Lgraph (gra (graphI I))
            ((agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l'))
            (cgra (graphI I)) (lgra (graphI I))\<^esub> la \<Longrightarrow>
       a @\<^bsub>Lgraph (gra (graphI I))
            ((agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l'))
            (cgra (graphI I)) (lgra (graphI I))\<^esub> l'a \<Longrightarrow>
       la = l'a"
      apply (case_tac "la \<noteq> l' \<and> la \<noteq> l \<and> l'a \<noteq> l' \<and> l'a \<noteq> l")
       apply (simp add: atI_def)
       apply (subgoal_tac "la = l' \<or> la = l \<or> l'a = l' \<or> l'a = l")
      prefer 2
      using assms(2) atI_def apply blast
      apply blast
      by (metis agra.simps assms(2) atI_def del_nodup fun_upd_apply)
  next show "\<And>(G::igraph) (Ia::infrastructure) (aa::char list) (l::location) (l'::location)
       I'a::infrastructure.
       I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor a) move \<Longrightarrow>
       a \<in> set (agra (graphI I) l) \<Longrightarrow>
       a \<notin> set (agra (graphI I) l') \<Longrightarrow>
       \<forall>la::location.
          (la = l \<longrightarrow> l \<noteq> l' \<longrightarrow> nodup a (del a (agra (graphI I) l))) \<and>
          (la \<noteq> l \<longrightarrow> la \<noteq> l' \<longrightarrow> nodup a (agra (graphI I) la))"
      by (simp add: assms(2) nodup_down)
  next show "\<And>(G::igraph) (Ia::infrastructure) (aa::char list) (l::location) (l'::location)
       I'a::infrastructure.
       I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor a) move \<Longrightarrow>
       (a \<in> set (agra (graphI I) l) \<longrightarrow> a \<in> set (agra (graphI I) l')) \<longrightarrow>
       (\<forall>(l::location) l'::location.
           a @\<^bsub>Lgraph (gra (graphI I)) (agra (graphI I)) (cgra (graphI I)) (lgra (graphI I))\<^esub> l \<and>
           a @\<^bsub>Lgraph (gra (graphI I)) (agra (graphI I)) (cgra (graphI I)) (lgra (graphI I))\<^esub> l' \<longrightarrow>
           l = l') \<and>
       (\<forall>l::location. nodup a (agra (graphI I) l))"
      by (simp add: assms(2) atI_def)
  next show "\<And>(G::igraph) (Ia::infrastructure) (aa::char list) (l::location) (l'::location)
       I'a::infrastructure.
       I = Ia \<Longrightarrow>
       I' =
       Infrastructure
        (Lgraph (gra (graphI Ia))
          (if aa \<in> set (agra (graphI Ia) l) \<and> aa \<notin> set (agra (graphI Ia) l')
           then (agra (graphI Ia))(l := del aa (agra (graphI Ia) l), l' := aa # agra (graphI Ia) l')
           else agra (graphI Ia))
          (cgra (graphI Ia)) (lgra (graphI Ia)))
        (delta Ia) \<Longrightarrow>
       G = graphI Ia \<Longrightarrow>
       aa @\<^bsub>graphI Ia\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI Ia) \<Longrightarrow>
       l' \<in> nodes (graphI Ia) \<Longrightarrow>
       aa \<in> actors_graph (graphI Ia) \<Longrightarrow>
       enables Ia l' (Actor aa) move \<Longrightarrow>
       I'a =
       Infrastructure
        (Lgraph (gra (graphI Ia))
          (if aa \<in> set (agra (graphI Ia) l) \<and> aa \<notin> set (agra (graphI Ia) l')
           then (agra (graphI Ia))(l := del aa (agra (graphI Ia) l), l' := aa # agra (graphI Ia) l')
           else agra (graphI Ia))
          (cgra (graphI Ia)) (lgra (graphI Ia)))
        (delta Ia) \<Longrightarrow>
       aa \<noteq> a \<longrightarrow>
       (aa \<in> set (agra (graphI Ia) l) \<and> aa \<notin> set (agra (graphI Ia) l') \<longrightarrow>
        (\<forall>(la::location) l'a::location.
            a @\<^bsub>Lgraph (gra (graphI Ia))
                 ((agra (graphI Ia))
                  (l := del aa (agra (graphI Ia) l), l' := aa # agra (graphI Ia) l'))
                 (cgra (graphI Ia)) (lgra (graphI Ia))\<^esub> la \<and>
            a @\<^bsub>Lgraph (gra (graphI Ia))
                 ((agra (graphI Ia))
                  (l := del aa (agra (graphI Ia) l), l' := aa # agra (graphI Ia) l'))
                 (cgra (graphI Ia)) (lgra (graphI Ia))\<^esub> l'a \<longrightarrow>
            la = l'a) \<and>
        (\<forall>la::location.
            (la = l \<longrightarrow>
             (l = l' \<longrightarrow> nodup a (agra (graphI Ia) l')) \<and>
             (l \<noteq> l' \<longrightarrow> nodup a (del aa (agra (graphI Ia) l)))) \<and>
            (la \<noteq> l \<longrightarrow>
             (la = l' \<longrightarrow> nodup a (agra (graphI Ia) l')) \<and>
             (la \<noteq> l' \<longrightarrow> nodup a (agra (graphI Ia) la))))) \<and>
       ((aa \<in> set (agra (graphI Ia) l) \<longrightarrow> aa \<in> set (agra (graphI Ia) l')) \<longrightarrow>
        (\<forall>(l::location) l'::location.
            a @\<^bsub>Lgraph (gra (graphI Ia)) (agra (graphI Ia)) (cgra (graphI Ia))
                 (lgra (graphI Ia))\<^esub> l \<and>
            a @\<^bsub>Lgraph (gra (graphI Ia)) (agra (graphI Ia)) (cgra (graphI Ia))
                 (lgra (graphI Ia))\<^esub> l' \<longrightarrow>
            l = l') \<and>
        (\<forall>l::location. nodup a (agra (graphI Ia) l)))"
    proof (clarify, simp add: atI_def,rule conjI,clarify,rule conjI,clarify,rule conjI,
           clarify,rule conjI,clarify,simp,clarify,rule conjI,(rule impI)+)
      show "\<And>(aa::char list) (l::location) (l'::location) l'a::location.
       I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          ((agra (graphI I))(l := del aa (agra (graphI I) l), l' := aa # agra (graphI I) l'))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       aa \<in> set (agra (graphI I) l) \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       aa \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor aa) move \<Longrightarrow>
       aa \<noteq> a \<Longrightarrow>
       aa \<notin> set (agra (graphI I) l') \<Longrightarrow>
       l \<noteq> l' \<Longrightarrow>
       l'a \<noteq> l \<Longrightarrow>
       l'a = l' \<Longrightarrow> a \<in> set (del aa (agra (graphI I) l)) \<Longrightarrow> a \<notin> set (agra (graphI I) l')"
        by (meson assms(2) atI_def del_notin_down)
    next show "\<And>(aa::char list) (l::location) (l'::location) l'a::location.
       I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          ((agra (graphI I))(l := del aa (agra (graphI I) l), l' := aa # agra (graphI I) l'))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       aa \<in> set (agra (graphI I) l) \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       aa \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor aa) move \<Longrightarrow>
       aa \<noteq> a \<Longrightarrow>
       aa \<notin> set (agra (graphI I) l') \<Longrightarrow>
       l \<noteq> l' \<Longrightarrow>
       l'a \<noteq> l \<Longrightarrow>
       l'a \<noteq> l' \<longrightarrow> a \<in> set (del aa (agra (graphI I) l)) \<longrightarrow> a \<notin> set (agra (graphI I) l'a)"
        by (meson assms(2) atI_def del_notin_down)
    next show "\<And>(aa::char list) (l::location) (l'::location) la::location.
       I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if aa \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del aa (agra (graphI I) l), l' := aa # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       aa \<in> set (agra (graphI I) l) \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       aa \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor aa) move \<Longrightarrow>
       aa \<noteq> a \<Longrightarrow>
       aa \<notin> set (agra (graphI I) l') \<Longrightarrow>
       la \<noteq> l \<longrightarrow>
       (la = l' \<longrightarrow>
        (\<forall>l'a::location.
            (l'a = l \<longrightarrow>
             l \<noteq> l' \<longrightarrow> a \<in> set (agra (graphI I) l') \<longrightarrow> a \<notin> set (del aa (agra (graphI I) l))) \<and>
            (l'a \<noteq> l \<longrightarrow>
             l'a \<noteq> l' \<longrightarrow> a \<in> set (agra (graphI I) l') \<longrightarrow> a \<notin> set (agra (graphI I) l'a)))) \<and>
       (la \<noteq> l' \<longrightarrow>
        (\<forall>l'a::location.
            (l'a = l \<longrightarrow>
             (l = l' \<longrightarrow> a \<in> set (agra (graphI I) la) \<longrightarrow> a \<notin> set (agra (graphI I) l')) \<and>
             (l \<noteq> l' \<longrightarrow> a \<in> set (agra (graphI I) la) \<longrightarrow> a \<notin> set (del aa (agra (graphI I) l)))) \<and>
            (l'a \<noteq> l \<longrightarrow>
             (l'a = l' \<longrightarrow> a \<in> set (agra (graphI I) la) \<longrightarrow> a \<notin> set (agra (graphI I) l')) \<and>
             (l'a \<noteq> l' \<longrightarrow>
              a \<in> set (agra (graphI I) la) \<and> a \<in> set (agra (graphI I) l'a) \<longrightarrow> la = l'a))))"
        by (meson assms(2) atI_def del_notin_down)
    next show "\<And>(aa::char list) (l::location) l'::location.
       I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if aa \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del aa (agra (graphI I) l), l' := aa # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       aa \<in> set (agra (graphI I) l) \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       aa \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor aa) move \<Longrightarrow>
       aa \<noteq> a \<Longrightarrow>
       aa \<notin> set (agra (graphI I) l') \<Longrightarrow>
       \<forall>la::location.
          (la = l \<longrightarrow>
           (l = l' \<longrightarrow> nodup a (agra (graphI I) l')) \<and>
           (l \<noteq> l' \<longrightarrow> nodup a (del aa (agra (graphI I) l)))) \<and>
          (la \<noteq> l \<longrightarrow>
           (la = l' \<longrightarrow> nodup a (agra (graphI I) l')) \<and> (la \<noteq> l' \<longrightarrow> nodup a (agra (graphI I) la)))"
        by (simp add: assms(2) nodup_down_notin)
    next show "\<And>(aa::char list) (l::location) l'::location.
       I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if aa \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del aa (agra (graphI I) l), l' := aa # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       aa \<in> set (agra (graphI I) l) \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       aa \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor aa) move \<Longrightarrow>
       aa \<noteq> a \<Longrightarrow>
       aa \<in> set (agra (graphI I) l') \<longrightarrow>
       (\<forall>(l::location) l'::location.
           a \<in> set (agra (graphI I) l) \<and> a \<in> set (agra (graphI I) l') \<longrightarrow> l = l') \<and>
       (\<forall>l::location. nodup a (agra (graphI I) l))"
        using assms(2) atI_def by blast
    qed
  qed
qed   


lemma actors_unique_loc_step: 
  assumes "(I, I') \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*" 
      and "\<forall> a. (\<forall> l l'. a @\<^bsub>graphI I\<^esub> l \<and> a @\<^bsub>graphI I\<^esub> l' \<longrightarrow> l = l')\<and>
          (\<forall> l. nodup a (agra (graphI I) l))" 
    shows   "\<forall> a. (\<forall> l l'. a @\<^bsub>graphI I'\<^esub> l \<and> a @\<^bsub>graphI I'\<^esub> l'  \<longrightarrow> l = l') \<and>
          (\<forall> l. nodup a (agra (graphI I') l))"
proof -
  have ind: "(\<forall> a. (\<forall> l l'. a @\<^bsub>graphI I\<^esub> l \<and> a @\<^bsub>graphI I\<^esub> l' \<longrightarrow> l = l')\<and>
          (\<forall> l. nodup a (agra (graphI I) l))) \<longrightarrow>
       (\<forall> a. (\<forall> l l'. a @\<^bsub>graphI I'\<^esub> l \<and> a @\<^bsub>graphI I'\<^esub> l'  \<longrightarrow> l = l') \<and>
          (\<forall> l. nodup a (agra (graphI I') l)))"
  proof (insert assms(1), erule rtrancl.induct)
    show "\<And>a::infrastructure.
       (\<forall>aa::char list.
           (\<forall>(l::location) l'::location. aa @\<^bsub>graphI a\<^esub> l \<and> aa @\<^bsub>graphI a\<^esub> l' \<longrightarrow> l = l') \<and>
           (\<forall>l::location. nodup aa (agra (graphI a) l))) \<longrightarrow>
       (\<forall>aa::char list.
           (\<forall>(l::location) l'::location. aa @\<^bsub>graphI a\<^esub> l \<and> aa @\<^bsub>graphI a\<^esub> l' \<longrightarrow> l = l') \<and>
           (\<forall>l::location. nodup aa (agra (graphI a) l)))" by simp
  next show "\<And>(a::infrastructure) (b::infrastructure) (c::infrastructure).
       (a, b) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       (\<forall>aa::char list.
           (\<forall>(l::location) (l'::location). (aa @\<^bsub>graphI a\<^esub> l \<and> aa @\<^bsub>graphI a\<^esub> l') \<longrightarrow> l = l') \<and>
           (\<forall>l::location. nodup aa (agra (graphI a) l))) \<longrightarrow>
       (\<forall>a::char list.
           (\<forall>(l::location) (l'::location). (a @\<^bsub>graphI b\<^esub> l \<and> a @\<^bsub>graphI b\<^esub> l') \<longrightarrow> l = l') \<and>
           (\<forall>l::location. nodup a (agra (graphI b) l))) \<Longrightarrow>
       (b, c) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
       (\<forall>aa::char list.
           (\<forall>(l::location) l'::location. (aa @\<^bsub>graphI a\<^esub> l \<and> aa @\<^bsub>graphI a\<^esub> l') \<longrightarrow> l = l') \<and>
           (\<forall>l::location. nodup aa (agra (graphI a) l))) \<longrightarrow>
       (\<forall>a::char list.
           (\<forall>(l::location) l'::location. (a @\<^bsub>graphI c\<^esub> l \<and> a @\<^bsub>graphI c\<^esub> l') \<longrightarrow> l = l') \<and>
           (\<forall>l::location. nodup a (agra (graphI c) l)))"
      by (rule impI, rule allI, rule actors_unique_loc_base, drule CollectD, 
             simp,erule impE, assumption, erule spec)   
  qed
  show ?thesis 
  by (insert ind, insert assms(2), simp)
qed

lemma actors_unique_loc_aid_base:"
 \<forall> a. (\<forall> l l'. a @\<^bsub>graphI Airplane_not_in_danger_init\<^esub> l \<and> 
               a @\<^bsub>graphI Airplane_not_in_danger_init\<^esub> l' \<longrightarrow> l = l')\<and>
         (\<forall> l. nodup a (agra (graphI Airplane_not_in_danger_init) l))"  
proof (simp add: Airplane_not_in_danger_init_def ex_graph_def, clarify, rule conjI, clarify,
      rule conjI, clarify, rule impI, (rule allI)+, rule impI, simp add: atI_def)
  show "\<And>(l::location) l'::location.
       ''Charly''
       \<in> set (if l = cockpit then [''Bob'', ''Charly'']
               else if l = door then [] else if l = cabin then [''Alice''] else []) \<and>
       ''Charly''
       \<in> set (if l' = cockpit then [''Bob'', ''Charly'']
               else if l' = door then [] else if l' = cabin then [''Alice''] else []) \<Longrightarrow>
       l = l'"
  by (case_tac "l = l'", assumption, rule FalseE, case_tac "l = cockpit \<or> l = door \<or> l = cabin",
      erule disjE, simp, case_tac "l' = door \<or> l' = cabin", erule disjE, simp, 
      simp add: cabin_def door_def, simp, erule disjE, simp add: door_def cockpit_def, 
      simp add: cabin_def door_def cockpit_def, simp)
next show "\<And>a::char list.
       ''Charly'' \<noteq> a \<longrightarrow>
       (\<forall>(l::location) l'::location.
           a @\<^bsub>Lgraph {(cockpit, door), (door, cabin)}
                (\<lambda>x::location.
                    if x = cockpit then [''Bob'', ''Charly'']
                    else if x = door then [] else if x = cabin then [''Alice''] else [])
                ex_creds ex_locs\<^esub> l \<and>
           a @\<^bsub>Lgraph {(cockpit, door), (door, cabin)}
                (\<lambda>x::location.
                    if x = cockpit then [''Bob'', ''Charly'']
                    else if x = door then [] else if x = cabin then [''Alice''] else [])
                ex_creds ex_locs\<^esub> l' \<longrightarrow>
           l = l')"
  by (clarify, simp add: atI_def, case_tac "l = l'", assumption, rule FalseE,
      case_tac "l = cockpit \<or> l = door \<or> l = cabin", erule disjE, simp,
      case_tac "l' = door \<or> l' = cabin", erule disjE, simp, simp add: cabin_def door_def,
      simp, erule disjE, simp add: door_def cockpit_def, case_tac "l = cockpit",
      simp add: cabin_def cockpit_def, simp add: cabin_def door_def, case_tac "l' = cockpit",
      simp, simp add: cabin_def, case_tac "l' = door", simp, simp add: cabin_def, simp)
qed

lemma actors_unique_loc_aid_step: 
"(Airplane_not_in_danger_init, I)\<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*
 \<Longrightarrow>     \<forall> a. (\<forall> l l'. a @\<^bsub>graphI I\<^esub> l \<and> a @\<^bsub>graphI I\<^esub> l' \<longrightarrow> l = l')\<and>
         (\<forall> l. nodup a (agra (graphI I) l))"  
  by (erule actors_unique_loc_step, rule actors_unique_loc_aid_base)
    
text \<open>Using the state transition, Kripke structure and CTL, we can now
   also express (and prove!) unreachability properties which enable to 
   formally verify security properties for specific policies, like two-person
   rule.\<close>
lemma Anid_airplane_actors: "actors_graph (graphI Airplane_not_in_danger_init) = airplane_actors"
proof (simp add: Airplane_not_in_danger_init_def ex_graph_def actors_graph_def nodes_def 
                 airplane_actors_def, rule equalityI)
  show "{x::char list.
     \<exists>y::location.
        (y = door \<longrightarrow>
         (door = cockpit \<longrightarrow>
          (\<exists>y::location. y = cockpit \<or> y = cabin \<or> y = cockpit \<or> y = cockpit \<and> cockpit = cabin) \<and>
          (x = ''Bob'' \<or> x = ''Charly'')) \<and>
         door = cockpit) \<and>
        (y \<noteq> door \<longrightarrow>
         (y = cockpit \<longrightarrow>
          (\<exists>y::location.
              y = door \<or>
              cockpit = door \<and> y = cabin \<or>
              y = cockpit \<and> cockpit = door \<or> y = door \<and> cockpit = cabin) \<and>
          (x = ''Bob'' \<or> x = ''Charly'')) \<and>
         (y \<noteq> cockpit \<longrightarrow> y = cabin \<and> x = ''Alice'' \<and> y = cabin))}
    \<subseteq> {''Bob'', ''Charly'', ''Alice''}"
  by (rule subsetI, drule CollectD, erule exE, (erule conjE)+,
      simp add: door_def cockpit_def cabin_def, (erule conjE)+, force)
next show "{''Bob'', ''Charly'', ''Alice''}
    \<subseteq> {x::char list.
        \<exists>y::location.
           (y = door \<longrightarrow>
            (door = cockpit \<longrightarrow>
             (\<exists>y::location.
                 y = cockpit \<or> y = cabin \<or> y = cockpit \<or> y = cockpit \<and> cockpit = cabin) \<and>
             (x = ''Bob'' \<or> x = ''Charly'')) \<and>
            door = cockpit) \<and>
           (y \<noteq> door \<longrightarrow>
            (y = cockpit \<longrightarrow>
             (\<exists>y::location.
                 y = door \<or>
                 cockpit = door \<and> y = cabin \<or>
                 y = cockpit \<and> cockpit = door \<or> y = door \<and> cockpit = cabin) \<and>
             (x = ''Bob'' \<or> x = ''Charly'')) \<and>
            (y \<noteq> cockpit \<longrightarrow> y = cabin \<and> x = ''Alice'' \<and> y = cabin))}"
  by (rule subsetI, rule CollectI, simp add: door_def cockpit_def cabin_def,
      case_tac "x = ''Bob''", force, case_tac "x = ''Charly''", force,
      subgoal_tac "x = ''Alice''", force, simp)    
qed

lemma all_airplane_actors: "(Airplane_not_in_danger_init, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
              \<Longrightarrow> actors_graph(graphI y) = airplane_actors"
  by (insert Anid_airplane_actors, erule subst, rule sym, erule same_actors)
      
lemma actors_at_loc_in_graph: "\<lbrakk> l \<in> nodes(graphI I); a  @\<^bsub>graphI I\<^esub> l\<rbrakk>
                                \<Longrightarrow> a \<in> actors_graph (graphI I)"
  by (simp add: atI_def actors_graph_def, rule exI, rule conjI)

lemma not_en_get_Apnid: 
  assumes "(Airplane_not_in_danger_init,y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*" 
  shows   "~(enables y l (Actor a) get)"
proof -
  have "delta y = delta(Airplane_not_in_danger_init)" 
  by (insert assms, rule sym, erule_tac init_state_policy)
  with assms show ?thesis 
    by (simp add: Airplane_not_in_danger_init_def enables_def local_policies_four_eyes_def)    
qed
 
lemma Apnid_tsp_test: "~(enables Airplane_not_in_danger_init cockpit (Actor ''Alice'') get)"    
  by (simp add: Airplane_not_in_danger_init_def ex_creds_def enables_def 
                local_policies_four_eyes_def cabin_def door_def cockpit_def 
                ex_graph_def ex_locs_def)

lemma Apnid_tsp_test_gen: "~(enables Airplane_not_in_danger_init l (Actor a) get)"    
  by (simp add: Airplane_not_in_danger_init_def ex_creds_def enables_def 
                local_policies_four_eyes_def cabin_def door_def cockpit_def 
                ex_graph_def ex_locs_def)

lemma test_graph_atI: "''Bob'' @\<^bsub>graphI Airplane_not_in_danger_init\<^esub> cockpit" 
  by (simp add: Airplane_not_in_danger_init_def ex_graph_def atI_def)  

text \<open>Invariant: number of staff in cockpit never below 2\<close>
lemma two_person_inv: 
  fixes z z' 
  assumes "(2::nat) \<le> length (agra (graphI z) cockpit)"
      and "nodes(graphI z) = nodes(graphI Airplane_not_in_danger_init)"
      and "delta(z) = delta(Airplane_not_in_danger_init)"
      and "(Airplane_not_in_danger_init,z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
      and "z \<rightarrow>\<^sub>n z'"
    shows "(2::nat) \<le> length (agra (graphI z') cockpit)"
proof (insert assms(5), erule state_transition_in.cases)
  show "\<And>(G::igraph) (I::infrastructure) (a::char list) (l::location) (a'::char list) (za::char list)
       I'::infrastructure.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       a' @\<^bsub>G\<^esub> l \<Longrightarrow>
       has G (Actor a, za) \<Longrightarrow>
       enables I l (Actor a) get \<Longrightarrow>
       I' =
       Infrastructure
        (Lgraph (gra G) (agra G)
          ((cgra G)(Actor a' := (za # fst (cgra G (Actor a')), snd (cgra G (Actor a'))))) (lgra G))
        (delta I) \<Longrightarrow>
       (2::nat) \<le> length (agra (graphI z') cockpit)" using assms by simp
next show "\<And>(G::igraph) (I::infrastructure) (a::char list) (l::location) (I'::infrastructure)
       za::char list.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       enables I l (Actor a) put \<Longrightarrow>
       I' = Infrastructure (Lgraph (gra G) (agra G) (cgra G) ((lgra G)(l := [za]))) (delta I) \<Longrightarrow>
       (2::nat) \<le> length (agra (graphI z') cockpit)" using assms by simp
next show "\<And>(G::igraph) (I::infrastructure) (l::location) (a::char list) (I'::infrastructure)
       za::char list.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       enables I l (Actor a) put \<Longrightarrow>
       I' = Infrastructure (Lgraph (gra G) (agra G) (cgra G) ((lgra G)(l := [za]))) (delta I) \<Longrightarrow>
       (2::nat) \<le> length (agra (graphI z') cockpit)" using assms by simp
next show "\<And>(G::igraph) (I::infrastructure) (a::char list) (l::location) (l'::location)
       I'::infrastructure.
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> nodes G \<Longrightarrow>
       l' \<in> nodes G \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor a) move \<Longrightarrow>
       I' = Infrastructure (move_graph_a a l l' (graphI I)) (delta I) \<Longrightarrow>
       (2::nat) \<le> length (agra (graphI z') cockpit)"
proof -
fix G :: igraph and I :: infrastructure and a :: "char list" and l :: location and l' :: location and I' :: infrastructure
  have f1: "UasI ''Eve'' ''Charly''"
    using Eve_precipitating_event Insider_Eve Insider_def by force
  obtain ccs :: "char list \<Rightarrow> char list" and ccsa :: "char list \<Rightarrow> char list" where
    f2: "\<forall>cs csa. (\<not> UasI cs csa \<or> Actor cs = Actor csa \<and> (\<forall>csa csb. (csa = cs \<or> csb = cs \<or> Actor csa \<noteq> Actor csb) \<or> csa = csb)) \<and> (UasI cs csa \<or> Actor cs \<noteq> Actor csa \<or> (ccs cs \<noteq> cs \<and> ccsa cs \<noteq> cs \<and> Actor (ccs cs) = Actor (ccsa cs)) \<and> ccs cs \<noteq> ccsa cs)"
    using UasI_def by moura
  have "''Bob'' @\<^bsub>graphI (Infrastructure ex_graph local_policies)\<^esub> Location 2"
    using Airplane_not_in_danger_init_def cockpit_def test_graph_atI by force
  then have "Actor ''Bob'' = Actor ''Eve''"
    using Airplane_scenario_def airplane.cockpit_foe_control airplane_axioms cockpit_def ex_inv3 global_policy_def by blast
  then show "2 \<le> length (agra (graphI z') cockpit)"
    using f2 f1 by auto
qed
qed

lemma two_person_inv1:
  assumes "(Airplane_not_in_danger_init,z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*" 
  shows "(2::nat) \<le> length (agra (graphI z) cockpit)"  
proof (insert assms, erule rtrancl_induct)
  show "(2::nat) \<le> length (agra (graphI Airplane_not_in_danger_init) cockpit)"
  by (simp add: Airplane_not_in_danger_init_def ex_graph_def)    
next show "\<And>(y::infrastructure) z::infrastructure.
       (Airplane_not_in_danger_init, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       (y, z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
       (2::nat) \<le> length (agra (graphI y) cockpit) \<Longrightarrow> (2::nat) \<le> length (agra (graphI z) cockpit)"
    by (rule two_person_inv, assumption, rule same_nodes, assumption, rule sym, 
        rule init_state_policy, assumption+, simp)
qed

text \<open>The version of two\_person\_inv above we need, uses cardinality of lists of 
   actors rather than length of lists. Therefore first some equivalences
   and then a restatement of two\_person\_inv in terms of sets\<close>
text \<open>proof idea: show since there are no duplicates in the list
    agra (graphI z) cockpit therefore then 
         card(set(agra (graphI z))) = length(agra (graphI z))\<close>
lemma nodup_card_insert: 
       "a \<notin> set l \<longrightarrow> card (insert a (set l)) = Suc (card (set l))"      
by auto
       
lemma no_dup_set_list_num_eq[rule_format]: 
    "(\<forall> a. nodup a l) \<longrightarrow> card (set l) = length l" 
  by (induct_tac l, simp, clarify, simp, erule impE, rule allI,
      drule_tac x = aa in spec, case_tac "a = aa", simp, erule nodup_notin, simp)
    
lemma two_person_set_inv: 
  assumes "(Airplane_not_in_danger_init,z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*" 
    shows "(2::nat) \<le> card (set (agra (graphI z) cockpit))"  
proof -
  have a: "card (set (agra (graphI z) cockpit)) = length(agra (graphI z) cockpit)"
   by (rule no_dup_set_list_num_eq, insert assms, drule actors_unique_loc_aid_step,
       drule_tac x = a in spec, erule conjE, erule_tac x = cockpit in spec)
  show ?thesis 
   by (insert a, erule ssubst, rule two_person_inv1, rule assms)
qed

lemma Pred_all_unique: "\<lbrakk> ? x. P x; (! x. P x \<longrightarrow> x = c)\<rbrakk> \<Longrightarrow> P c"
  by (case_tac "P c", assumption, erule exE, drule_tac x = x in spec,
      drule mp, assumption, erule subst) 
              
lemma Set_all_unique: "\<lbrakk> S \<noteq> {}; (\<forall> x \<in> S. x = c) \<rbrakk> \<Longrightarrow> c \<in> S"
  by (rule_tac P = "\<lambda> x. x \<in> S" in Pred_all_unique, force, simp)
    
lemma airplane_actors_inv0[rule_format]: 
    "\<forall> z z'. (\<forall>h::char list \<in> set (agra (graphI z) cockpit). h \<in> airplane_actors) \<and> 
          (Airplane_not_in_danger_init,z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<and>
            z \<rightarrow>\<^sub>n z' \<longrightarrow>  (\<forall>h::char list\<in>set (agra (graphI z') cockpit). h \<in> airplane_actors)"     
proof (clarify, erule state_transition_in.cases)
  show " \<And>(z::infrastructure) (z'::infrastructure) (h::char list) (G::igraph) (I::infrastructure)
       (a::char list) (l::location) (a'::char list) (za::char list) I'::infrastructure.
       h \<in> set (agra (graphI z') cockpit) \<Longrightarrow>
       \<forall>h::char list\<in>set (agra (graphI z) cockpit). h \<in> airplane_actors \<Longrightarrow>
       (Airplane_not_in_danger_init, z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       a' @\<^bsub>G\<^esub> l \<Longrightarrow>
       has G (Actor a, za) \<Longrightarrow>
       enables I l (Actor a) get \<Longrightarrow>
       I' =
       Infrastructure
        (Lgraph (gra G) (agra G)
          ((cgra G)(Actor a' := (za # fst (cgra G (Actor a')), snd (cgra G (Actor a'))))) (lgra G))
        (delta I) \<Longrightarrow>
       h \<in> airplane_actors"
    by simp
next show "\<And>(z::infrastructure) (z'::infrastructure) (h::char list) (G::igraph) (I::infrastructure)
       (a::char list) (l::location) (I'::infrastructure) za::char list.
       h \<in> set (agra (graphI z') cockpit) \<Longrightarrow>
       \<forall>h::char list\<in>set (agra (graphI z) cockpit). h \<in> airplane_actors \<Longrightarrow>
       (Airplane_not_in_danger_init, z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       enables I l (Actor a) put \<Longrightarrow>
       I' = Infrastructure (Lgraph (gra G) (agra G) (cgra G) ((lgra G)(l := [za]))) (delta I) \<Longrightarrow>
       h \<in> airplane_actors" 
    by simp
next show "\<And>(z::infrastructure) (z'::infrastructure) (h::char list) (G::igraph) (I::infrastructure)
       (l::location) (a::char list) (I'::infrastructure) za::char list.
       h \<in> set (agra (graphI z') cockpit) \<Longrightarrow>
       \<forall>h::char list\<in>set (agra (graphI z) cockpit). h \<in> airplane_actors \<Longrightarrow>
       (Airplane_not_in_danger_init, z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       enables I l (Actor a) put \<Longrightarrow>
       I' = Infrastructure (Lgraph (gra G) (agra G) (cgra G) ((lgra G)(l := [za]))) (delta I) \<Longrightarrow>
       h \<in> airplane_actors"
    by simp
next show "\<And>(z::infrastructure) (z'::infrastructure) (h::char list) (G::igraph) (I::infrastructure)
       (a::char list) (l::location) (l'::location) I'::infrastructure.
       h \<in> set (agra (graphI z') cockpit) \<Longrightarrow>
       \<forall>h::char list\<in>set (agra (graphI z) cockpit). h \<in> airplane_actors \<Longrightarrow>
       (Airplane_not_in_danger_init, z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>G\<^esub> l \<Longrightarrow>
       l \<in> nodes G \<Longrightarrow>
       l' \<in> nodes G \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor a) move \<Longrightarrow>
       I' = Infrastructure (move_graph_a a l l' (graphI I)) (delta I) \<Longrightarrow> h \<in> airplane_actors"
  proof (simp add: move_graph_a_def,
         case_tac "a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')")
    show "\<And>(z::infrastructure) (z'::infrastructure) (h::char list) (G::igraph) (I::infrastructure)
       (a::char list) (l::location) (l'::location) I'::infrastructure.
       h \<in> set ((if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
                  then (agra (graphI I))
                       (l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
                  else agra (graphI I))
                  cockpit) \<Longrightarrow>
       \<forall>h::char list\<in>set (agra (graphI I) cockpit). h \<in> airplane_actors \<Longrightarrow>
       (Airplane_not_in_danger_init, I) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor a) move \<Longrightarrow>
       I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       \<not> (a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')) \<Longrightarrow> h \<in> airplane_actors"
      by simp
  next show "\<And>(z::infrastructure) (z'::infrastructure) (h::char list) (G::igraph) (I::infrastructure)
       (a::char list) (l::location) (l'::location) I'::infrastructure.
       h \<in> set ((if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
                  then (agra (graphI I))
                       (l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
                  else agra (graphI I))
                  cockpit) \<Longrightarrow>
       \<forall>h::char list\<in>set (agra (graphI I) cockpit). h \<in> airplane_actors \<Longrightarrow>
       (Airplane_not_in_danger_init, I) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor a) move \<Longrightarrow>
       I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l') \<Longrightarrow> h \<in> airplane_actors"
    proof (case_tac "l' = cockpit")
      show "\<And>(z::infrastructure) (z'::infrastructure) (h::char list) (G::igraph) (I::infrastructure)
       (a::char list) (l::location) (l'::location) I'::infrastructure.
       h \<in> set ((if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
                  then (agra (graphI I))
                       (l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
                  else agra (graphI I))
                  cockpit) \<Longrightarrow>
       \<forall>h::char list\<in>set (agra (graphI I) cockpit). h \<in> airplane_actors \<Longrightarrow>
       (Airplane_not_in_danger_init, I) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor a) move \<Longrightarrow>
       I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l') \<Longrightarrow>
       l' \<noteq> cockpit \<Longrightarrow> h \<in> airplane_actors"
      proof (case_tac "cockpit = l")
        show "\<And>(z::infrastructure) (z'::infrastructure) (h::char list) (G::igraph) (I::infrastructure)
       (a::char list) (l::location) (l'::location) I'::infrastructure.
       h \<in> set ((if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
                  then (agra (graphI I))
                       (l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
                  else agra (graphI I))
                  cockpit) \<Longrightarrow>
       \<forall>h::char list\<in>set (agra (graphI I) cockpit). h \<in> airplane_actors \<Longrightarrow>
       (Airplane_not_in_danger_init, I) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor a) move \<Longrightarrow>
       I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l') \<Longrightarrow>
       l' \<noteq> cockpit \<Longrightarrow> cockpit \<noteq> l \<Longrightarrow> h \<in> airplane_actors"
          by simp
      next show " \<And>(z::infrastructure) (z'::infrastructure) (h::char list) (G::igraph) (I::infrastructure)
       (a::char list) (l::location) (l'::location) I'::infrastructure.
       h \<in> set ((if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
                  then (agra (graphI I))
                       (l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
                  else agra (graphI I))
                  cockpit) \<Longrightarrow>
       \<forall>h::char list\<in>set (agra (graphI I) cockpit). h \<in> airplane_actors \<Longrightarrow>
       (Airplane_not_in_danger_init, I) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor a) move \<Longrightarrow>
       I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l') \<Longrightarrow>
       l' \<noteq> cockpit \<Longrightarrow> cockpit = l \<Longrightarrow> h \<in> airplane_actors"
          by (simp, erule bspec, erule del_up)
      qed
    next show "\<And>(z::infrastructure) (z'::infrastructure) (h::char list) (G::igraph) (I::infrastructure)
       (a::char list) (l::location) (l'::location) I'::infrastructure.
       h \<in> set ((if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
                  then (agra (graphI I))
                       (l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
                  else agra (graphI I))
                  cockpit) \<Longrightarrow>
       \<forall>h::char list\<in>set (agra (graphI I) cockpit). h \<in> airplane_actors \<Longrightarrow>
       (Airplane_not_in_danger_init, I) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor a) move \<Longrightarrow>
       I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          (if a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l')
           then (agra (graphI I))(l := del a (agra (graphI I) l), l' := a # agra (graphI I) l')
           else agra (graphI I))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) l') \<Longrightarrow>
       l' = cockpit \<Longrightarrow> h \<in> airplane_actors"
      proof (simp, erule disjE)
        show "\<And>(z::infrastructure) (z'::infrastructure) (h::char list) (G::igraph) (I::infrastructure)
       (a::char list) (l::location) (l'::location) I'::infrastructure.
       \<forall>h::char list\<in>set (agra (graphI I) cockpit). h \<in> airplane_actors \<Longrightarrow>
       (Airplane_not_in_danger_init, I) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       z = I \<Longrightarrow>
       z' =
       Infrastructure
        (Lgraph (gra (graphI I))
          ((agra (graphI I))
           (l := del a (agra (graphI I) l), cockpit := a # agra (graphI I) cockpit))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       a @\<^bsub>graphI I\<^esub> l \<Longrightarrow>
       l \<in> nodes (graphI I) \<Longrightarrow>
       cockpit \<in> nodes (graphI I) \<Longrightarrow>
       a \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I cockpit (Actor a) move \<Longrightarrow>
       I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          ((agra (graphI I))
           (l := del a (agra (graphI I) l), cockpit := a # agra (graphI I) cockpit))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I) \<Longrightarrow>
       a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) cockpit) \<Longrightarrow>
       l' = cockpit \<Longrightarrow> h \<in> set (agra (graphI I) cockpit) \<Longrightarrow> h \<in> airplane_actors"
          by (erule bspec)
      next fix z z' h G I a l l' I'
        assume a0: "\<forall>h::char list\<in>set (agra (graphI I) cockpit). h \<in> airplane_actors"
      and a1: "(Airplane_not_in_danger_init, I) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"       
      and a2: "z = I"
      and a3: "z' =
       Infrastructure
        (Lgraph (gra (graphI I))
          ((agra (graphI I))
           (l := del a (agra (graphI I) l), cockpit := a # agra (graphI I) cockpit))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I)"
      and a4: "G = graphI I"
      and a5: "a @\<^bsub>graphI I\<^esub> l"
      and a6: "l \<in> nodes (graphI I)"
      and a7: "cockpit \<in> nodes (graphI I)"
      and a8: "a \<in> actors_graph (graphI I)"
      and a9: "enables I cockpit (Actor a) move"
      and a10: "I' =
       Infrastructure
        (Lgraph (gra (graphI I))
          ((agra (graphI I))
           (l := del a (agra (graphI I) l), cockpit := a # agra (graphI I) cockpit))
          (cgra (graphI I)) (lgra (graphI I)))
        (delta I)"
       and a11: "a \<in> set (agra (graphI I) l) \<and> a \<notin> set (agra (graphI I) cockpit)"
       and a12: "l' = cockpit" 
       and a13: "h = a"
        show  "h \<in> airplane_actors"
       proof -
       have a: "delta(I) = delta(Airplane_not_in_danger_init)"
         by (rule sym, rule init_state_policy, rule a1)
       show ?thesis 
         by (insert a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a,
             simp add: enables_def, erule bexE, simp add: Airplane_not_in_danger_init_def,
             unfold local_policies_four_eyes_def, simp, erule disjE, simp+,
             (* same trick as above show what Eve is not in the graph *)  
             erule exE, (erule conjE)+,  
             fold local_policies_four_eyes_def Airplane_not_in_danger_init_def,
             drule all_airplane_actors, erule subst)
     qed
   qed
 qed
qed
qed


lemma airplane_actors_inv: 
  assumes "(Airplane_not_in_danger_init,z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*" 
    shows "\<forall>h::char list\<in>set (agra (graphI z) cockpit). h \<in> airplane_actors"     
proof -
  have ind: "(Airplane_not_in_danger_init, z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<longrightarrow>
    (\<forall>h::char list\<in>set (agra (graphI z) cockpit). h \<in> airplane_actors)"
  proof (insert assms, erule rtrancl_induct)
    show "(Airplane_not_in_danger_init, Airplane_not_in_danger_init) \<in> {(x,y). x \<rightarrow>\<^sub>n y}\<^sup>* \<longrightarrow>
    (\<forall>h::char list\<in>set (agra (graphI Airplane_not_in_danger_init) cockpit). h \<in> airplane_actors)"
     by (rule impI, rule ballI,
         simp add: Airplane_not_in_danger_init_def ex_graph_def airplane_actors_def ex_locs_def, 
         blast)
    next show "\<And>(y::infrastructure) z::infrastructure.
       (Airplane_not_in_danger_init, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       (y, z) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
       (Airplane_not_in_danger_init, y) \<in> {(x,y). x \<rightarrow>\<^sub>n y}\<^sup>* \<longrightarrow>
       (\<forall>h::char list\<in>set (agra (graphI y) cockpit). h \<in> airplane_actors) \<Longrightarrow>
       (Airplane_not_in_danger_init, z) \<in> {(x,y). x \<rightarrow>\<^sub>n y}\<^sup>* \<longrightarrow>
       (\<forall>h::char list\<in>set (agra (graphI z) cockpit). h \<in> airplane_actors)"
    by (rule impI, rule ballI, rule_tac z = y in airplane_actors_inv0, 
        rule conjI, erule impE, assumption+, simp)
  qed
  show ?thesis 
  by (insert ind, insert assms, simp)
qed
    
lemma Eve_not_in_cockpit: "(Airplane_not_in_danger_init, I)
       \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       x \<in> set (agra (graphI I) cockpit) \<Longrightarrow> x \<noteq> ''Eve''"
 by (drule airplane_actors_inv, simp add: airplane_actors_def,
     drule_tac x = x in bspec, assumption, force)
    
text \<open>2 person invariant implies that there is always some x in cockpit x not equal Eve\<close>
lemma tp_imp_control:
  assumes "(Airplane_not_in_danger_init,I) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
  shows "(? x :: identity.  x @\<^bsub>graphI I\<^esub> cockpit \<and> Actor x \<noteq> Actor ''Eve'')"
proof -
  have a0: "(2::nat) \<le> card (set (agra (graphI I) cockpit))" 
    by (insert assms, erule two_person_set_inv)
  have a1: "is_singleton({''Charly''})"
    by (rule is_singletonI)
  have a6: "\<not>(\<forall> x \<in> set(agra (graphI I) cockpit). (Actor x = Actor ''Eve''))"
    proof (rule notI)
      assume a7: " \<forall>x::char list\<in>set (agra (graphI I) cockpit). Actor x = Actor ''Eve''"
      have a5: "\<forall>x::char list\<in>set (agra (graphI I) cockpit). x = ''Charly''"
        by (insert assms a0 a7, rule ballI, drule_tac x = x in bspec, assumption, 
            subgoal_tac "x \<noteq> ''Eve''", insert Insider_Eve, unfold Insider_def, (drule mp), 
               rule Eve_precipitating_event, simp add: UasI_def, erule Eve_not_in_cockpit)
      have a4: "set (agra (graphI I) cockpit) = {''Charly''}"
        by (rule equalityI, rule subsetI, insert a5, simp,
            rule subsetI, simp, rule Set_all_unique, insert a0, force, rule a5)
      have a2: "(card((set (agra (graphI I) cockpit)) :: char list set)) = (1 :: nat)"
         by (insert a1, unfold is_singleton_altdef, erule ssubst, insert a4, erule ssubst,
             fold is_singleton_altdef, rule a1)
      have a3: "(2 :: nat) \<le> (1 ::nat)" 
         by (insert a0, insert a2, erule subst, assumption) 
      show False
        by (insert a5 a4 a3 a2, arith)
    qed
  show ?thesis  by (insert assms a0 a6, simp add: atI_def, blast)
qed

lemma Fend_2:    "(Airplane_not_in_danger_init,I) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
         \<not> enables I cockpit (Actor ''Eve'') put"
  by (insert cockpit_foe_control, simp add: foe_control_def, drule_tac x = I in spec,
      erule mp, erule tp_imp_control)

theorem Four_eyes_no_danger: "Air_tp_Kripke \<turnstile> AG ({x. global_policy x ''Eve''})"
proof (simp add: Air_tp_Kripke_def check_def, rule conjI)
  show "Airplane_not_in_danger_init \<in> Air_tp_states"
    by (simp add: Airplane_not_in_danger_init_def Air_tp_states_def
                    state_transition_in_refl_def)
next show "Airplane_not_in_danger_init \<in> AG {x::infrastructure. global_policy x ''Eve''}"
  proof (unfold AG_def, simp add: gfp_def,
   rule_tac x = "{(x :: infrastructure) \<in> states Air_tp_Kripke. ~(''Eve'' @\<^bsub>graphI x\<^esub> cockpit)}" in exI,
   rule conjI)
    show "{x::infrastructure \<in> states Air_tp_Kripke. \<not> ''Eve'' @\<^bsub>graphI x\<^esub> cockpit}
    \<subseteq> {x::infrastructure. global_policy x ''Eve''}"
     by (unfold global_policy_def, simp add: airplane_actors_def, rule subsetI,
         drule CollectD, rule CollectI, erule conjE,
         simp add: Air_tp_Kripke_def Air_tp_states_def state_transition_in_refl_def,
         erule Fend_2)
 next show "{x::infrastructure \<in> states Air_tp_Kripke. \<not> ''Eve'' @\<^bsub>graphI x\<^esub> cockpit}
    \<subseteq> AX {x::infrastructure \<in> states Air_tp_Kripke. \<not> ''Eve'' @\<^bsub>graphI x\<^esub> cockpit} \<and>
    Airplane_not_in_danger_init
    \<in> {x::infrastructure \<in> states Air_tp_Kripke. \<not> ''Eve'' @\<^bsub>graphI x\<^esub> cockpit}"
   proof
     show "Airplane_not_in_danger_init
          \<in> {x::infrastructure \<in> states Air_tp_Kripke. \<not> ''Eve'' @\<^bsub>graphI x\<^esub> cockpit}"
      by (simp add: Airplane_not_in_danger_init_def Air_tp_Kripke_def Air_tp_states_def
                    state_transition_refl_def ex_graph_def atI_def Air_tp_Kripke_def
                    state_transition_in_refl_def)
  next show "{x::infrastructure \<in> states Air_tp_Kripke. \<not> ''Eve'' @\<^bsub>graphI x\<^esub> cockpit}
    \<subseteq> AX {x::infrastructure \<in> states Air_tp_Kripke. \<not> ''Eve'' @\<^bsub>graphI x\<^esub> cockpit}"
    proof (rule subsetI, simp add: AX_def, rule subsetI, rule CollectI, rule conjI)
      show "\<And>(x::infrastructure) xa::infrastructure.
       x \<in> states Air_tp_Kripke \<and> \<not> ''Eve'' @\<^bsub>graphI x\<^esub> cockpit \<Longrightarrow>
       xa \<in> Collect (state_transition x) \<Longrightarrow> xa \<in> states Air_tp_Kripke"
        by (simp add:  Air_tp_Kripke_def Air_tp_states_def state_transition_in_refl_def,
            simp add: atI_def, erule conjE,
            unfold state_transition_infra_def state_transition_in_refl_def,
            erule rtrancl_into_rtrancl, rule CollectI, simp)
    next fix x xa
        assume a0: "x \<in> states Air_tp_Kripke \<and> \<not> ''Eve'' @\<^bsub>graphI x\<^esub> cockpit"
         and a1: "xa \<in> Collect (state_transition x)"
        show "\<not> ''Eve'' @\<^bsub>graphI xa\<^esub> cockpit"
      proof -
        have b: "(Airplane_not_in_danger_init, xa)
       \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
        proof (insert a0 a1, rule rtrancl_trans)
          show "x \<in> states Air_tp_Kripke \<and> \<not> ''Eve'' @\<^bsub>graphI x\<^esub> cockpit \<Longrightarrow>
                xa \<in> Collect (state_transition x) \<Longrightarrow>
                (x, xa) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
            by (unfold state_transition_infra_def, force)
        next show "x \<in> states Air_tp_Kripke \<and> \<not> ''Eve'' @\<^bsub>graphI x\<^esub> cockpit \<Longrightarrow>
                  xa \<in> Collect (state_transition x) \<Longrightarrow>
                  (Airplane_not_in_danger_init, x) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>*"
            by (erule conjE, simp add: Air_tp_Kripke_def Air_tp_states_def state_transition_in_refl_def)+
        qed
        show ?thesis 
         by (insert a0 a1 b, rule_tac P = "''Eve'' @\<^bsub>graphI xa\<^esub> cockpit" in notI, 
            simp add: atI_def, drule Eve_not_in_cockpit, assumption, simp)
     qed       
   qed
 qed
qed
qed

end


text \<open>In the following we construct an instance of the locale airplane and proof
   that it is an interpretation. This serves the validation.\<close> 
definition airplane_actors_def': "airplane_actors \<equiv> {''Bob'', ''Charly'', ''Alice''}"
definition airplane_locations_def': 
"airplane_locations \<equiv> {Location 0, Location 1, Location 2}"
definition cockpit_def': "cockpit \<equiv> Location 2"
definition door_def': "door \<equiv> Location 1" 
definition cabin_def': "cabin \<equiv> Location 0" 
definition global_policy_def': "global_policy I a \<equiv> a \<notin> airplane_actors 
                 \<longrightarrow> \<not>(enables I cockpit (Actor a) put)"
definition ex_creds_def': "ex_creds \<equiv> 
        (\<lambda> x.(if x = Actor ''Bob'' 
              then ([''PIN''], [''pilot''])        
              else (if x = Actor ''Charly'' 
                    then ([''PIN''],[''copilot''])
                    else (if x = Actor ''Alice''  
                          then ([''PIN''],[''flightattendant''])
                                else ([],[])))))"

definition ex_locs_def': "ex_locs \<equiv>  (\<lambda> x. if x = door then [''norm''] else 
                                       (if x = cockpit then [''air''] else []))"
  
definition ex_locs'_def': "ex_locs' \<equiv>  (\<lambda> x. if x = door then [''locked''] else
                                         (if x = cockpit then [''air''] else []))"
  
definition ex_graph_def': "ex_graph \<equiv> Lgraph
      {(cockpit, door),(door,cabin)}
      (\<lambda> x. if x = cockpit then [''Bob'', ''Charly''] 
            else (if x = door then [] 
                  else (if x = cabin then [''Alice''] else [])))
      ex_creds ex_locs"

definition aid_graph_def': "aid_graph \<equiv>  Lgraph
      {(cockpit, door),(door,cabin)}
      (\<lambda> x. if x = cockpit then [''Charly''] 
            else (if x = door then [] 
                  else (if x = cabin then [''Bob'', ''Alice''] else [])))
      ex_creds ex_locs'"
  
definition aid_graph0_def': "aid_graph0 \<equiv>  Lgraph
      {(cockpit, door),(door,cabin)}
      (\<lambda> x. if x = cockpit then [''Charly''] 
            else (if x = door then [''Bob''] 
                  else (if x = cabin then [''Alice''] else [])))
        ex_creds ex_locs"

definition agid_graph_def': "agid_graph \<equiv>  Lgraph
      {(cockpit, door),(door,cabin)}
      (\<lambda> x. if x = cockpit then [''Charly''] 
            else (if x = door then [] 
                  else (if x = cabin then [''Bob'', ''Alice''] else [])))
      ex_creds ex_locs"
  
definition local_policies_def': "local_policies G \<equiv>  
   (\<lambda> y. if y = cockpit then
             {(\<lambda> x. (? n. (n @\<^bsub>G\<^esub> cockpit) \<and> Actor n = x), {put}),
              (\<lambda> x. (? n. (n @\<^bsub>G\<^esub> cabin) \<and> Actor n = x \<and> has G (x, ''PIN'')
                    \<and> isin G door ''norm''),{move})
             }
         else (if y = door then {(\<lambda> x. True, {move}),
                       (\<lambda> x. (? n. (n @\<^bsub>G\<^esub> cockpit) \<and> Actor n = x), {put})}
               else (if y = cabin then {(\<lambda> x. True, {move})} 
                     else {})))"
definition local_policies_four_eyes_def': "local_policies_four_eyes G \<equiv>  
   (\<lambda> y. if y = cockpit then
             {(\<lambda> x.  (? n. (n @\<^bsub>G\<^esub> cockpit) \<and> Actor n = x) \<and>
                     2 \<le> length(agra G y) \<and> (\<forall> h \<in> set(agra G y). h \<in> airplane_actors), {put}),
              (\<lambda> x. (? n. (n @\<^bsub>G\<^esub> cabin) \<and> Actor n = x \<and> has G (x, ''PIN'') \<and> 
                           isin G door ''norm'' ),{move})
             }
         else (if y = door then 
              {(\<lambda> x.  ((? n. (n @\<^bsub>G\<^esub> cockpit) \<and> Actor n = x) \<and> 3 \<le> length(agra G cockpit)), {move})}
               else (if y = cabin then 
                     {(\<lambda> x. ((? n. (n @\<^bsub>G\<^esub> door) \<and> Actor n = x)), {move})} 
                           else {})))"

definition Airplane_scenario_def':
"Airplane_scenario \<equiv> Infrastructure ex_graph local_policies"

definition Airplane_in_danger_def':
"Airplane_in_danger \<equiv> Infrastructure aid_graph local_policies"

text \<open>Intermediate step where pilot left cockpit but door still in
   norm position\<close>
definition Airplane_getting_in_danger0_def':
"Airplane_getting_in_danger0 \<equiv> Infrastructure aid_graph0 local_policies"

definition Airplane_getting_in_danger_def':
"Airplane_getting_in_danger \<equiv> Infrastructure agid_graph local_policies"

definition Air_states_def': "Air_states \<equiv> { I. Airplane_scenario \<rightarrow>\<^sub>n* I }"

definition Air_Kripke_def': "Air_Kripke \<equiv> Kripke Air_states {Airplane_scenario}"

definition Airplane_not_in_danger_def': 
"Airplane_not_in_danger \<equiv> Infrastructure aid_graph local_policies_four_eyes"

definition Airplane_not_in_danger_init_def':
"Airplane_not_in_danger_init \<equiv> Infrastructure ex_graph local_policies_four_eyes"

definition Air_tp_states_def': "Air_tp_states \<equiv> { I. Airplane_not_in_danger_init \<rightarrow>\<^sub>n* I }"

definition Air_tp_Kripke_def':
"Air_tp_Kripke \<equiv> Kripke Air_tp_states {Airplane_not_in_danger_init}"

definition Safety_def': "Safety I a \<equiv> a \<in> airplane_actors  
                       \<longrightarrow> (enables I cockpit (Actor a) move)"

definition Security_def': "Security I a \<equiv>  (isin (graphI I) door ''locked'') 
                       \<longrightarrow> \<not>(enables I cockpit (Actor a) move)"

definition foe_control_def': "foe_control l c \<equiv>  
   (! I:: infrastructure. (? x :: identity. 
        x @\<^bsub>graphI I\<^esub> l \<and> Actor x \<noteq> Actor ''Eve'')
             \<longrightarrow> \<not>(enables I l (Actor ''Eve'') c))"

definition astate_def': "astate x \<equiv>  
          (case x of 
           ''Eve'' \<Rightarrow> Actor_state depressed {revenge, peer_recognition}
          | _ \<Rightarrow> Actor_state happy {})"

print_interps airplane

text \<open>The additional assumption identified in the case study needs to be given as an axiom\<close>
axiomatization where
cockpit_foe_control': "foe_control cockpit put"

text \<open>(The following addresses the issue of redefining an abstract type.
   We experimented with suggestion given here: Makarius Wenzel,
   Re: [isabelle] typedecl versus explicit type parameters,
   Isabelle users mailing list, 2009,
   https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2009-July/msg00111.html.  
   )
  We furthermore need axiomatization to add the missing semantics to the
  abstractly declared type actor and thereby be able to redefine consts Actor.
  Since the function Actor has also been defined as a consts :: identity => actor
  as an abstract function without a definition, we now also now add its semantics
  mimicking some of the concepts of the conservative type definition of HOL.
  The alternative method of using a Locale to replace the abstract type\_decl actor
  in the AirInsider is a more elegant method for representing and abstract 
  type actor but it is not working properly for our framwework since it necessitates 
  introducing a type parameter 'actor into infrastructures which then makes it 
  impossible to instantiate them to the typeclass state in order to use CTL and 
  Kripke and the generic state transition. 
  Therefore, we go the former way of a post-hoc axiomatic redefinition of the 
  abstract type actor by using axiomatization of the existing Locale "type\_definition".
  This is done in the following. It allows to abstractedly assume as an axiom
  that there is a type definition for the abstract type actor. Adding a suitable
  definition of a representation for this type then additionally enables to introduce
  a definition for the function Actor (again using axiomatization to enforce the new
  definition).\<close>
   
definition Actor_Abs :: "identity \<Rightarrow> identity option"
  where 
"Actor_Abs x \<equiv> (if x \<in> {''Eve'', ''Charly''} then None else Some x)"

lemma UasI_ActorAbs: "Actor_Abs ''Eve'' = Actor_Abs ''Charly'' \<and>
    (\<forall>(x::char list) y::char list. x \<noteq> ''Eve'' \<and> y \<noteq> ''Eve'' \<and> Actor_Abs x = Actor_Abs y \<longrightarrow> x = y)"
  by (simp add: Actor_Abs_def)

lemma Actor_Abs_ran: "Actor_Abs x \<in> {y :: identity option. y \<in> Some ` {x :: identity. x \<notin> {''Eve'', ''Charly''}}| y = None}"
  by (simp add: Actor_Abs_def)

text \<open> With the following axiomatization, we can simulate the abstract type actor
   and postulate some unspecified Abs and Rep functions between it and the
   simulated identity option subtype.\<close>
axiomatization where Actor_type_def: 
"type_definition (Rep :: actor \<Rightarrow> identity option)(Abs :: identity option \<Rightarrow> actor) 
{y :: identity option. y \<in> Some ` {x :: identity. x \<notin> {''Eve'', ''Charly''}}| y = None}"

lemma Abs_inj_on: "\<And> Abs Rep:: actor \<Rightarrow> char list option. x \<in> {y :: identity option. y \<in> Some ` {x :: identity. x \<notin> {''Eve'', ''Charly''}}| y = None}  
               \<Longrightarrow> y \<in> {y :: identity option. y \<in> Some ` {x :: identity. x \<notin> {''Eve'', ''Charly''}}| y = None}
               \<Longrightarrow> (Abs :: char list option \<Rightarrow> actor) x = Abs y \<Longrightarrow> x = y"
by (insert Actor_type_def, drule_tac x = Rep in meta_spec, drule_tac x = Abs in meta_spec,
   frule_tac x = "Abs x" and y = "Abs y" in type_definition.Rep_inject,
   subgoal_tac "(Rep (Abs x) = Rep (Abs y))", subgoal_tac "Rep (Abs x) = x",
   subgoal_tac "Rep (Abs y) = y", erule subst, erule subst, assumption,
   (erule type_definition.Abs_inverse, assumption)+, simp)

lemma Actor_td_Abs_inverse: 
"(y\<in> {y :: identity option. y \<in> Some ` {x :: identity. x \<notin> {''Eve'', ''Charly''}}| y = None}) \<Longrightarrow> 
(Rep :: actor \<Rightarrow> identity option)((Abs :: identity option \<Rightarrow> actor) y) = y"
by (insert Actor_type_def, drule_tac x = Rep in meta_spec, drule_tac x = Abs in meta_spec,
  erule type_definition.Abs_inverse, assumption)

text \<open>Now, we can redefine the function Actor using a second axiomatization\<close>
axiomatization where Actor_redef: "Actor = (Abs :: identity option \<Rightarrow> actor)o Actor_Abs"

text \<open>need to show that 
@{term "Abs(Actor_Abs x) = Abs(Actor_Abs y) \<longrightarrow> Actor_Abs x = Actor_Abs y"},
i.e. @{text "injective Abs"}. 
Generally, Abs is not injective but @{text "injective_on"} the type predicate.
So, need to show that for any x, @{text "Actor_Abs x"} is in the type predicate, then it would follow.
What is the type predicate?
@{term "{y :: identity option. y \<in> Some`{x :: identity. x \<notin> {''Eve'', ''Charly''}} | y = None}"}\<close>
lemma UasI_Actor_redef: 
"\<And> Abs Rep:: actor \<Rightarrow> char list option. 
((Abs :: identity option \<Rightarrow> actor)o Actor_Abs) ''Eve'' = ((Abs :: identity option \<Rightarrow> actor)o Actor_Abs) ''Charly'' \<and>
    (\<forall>(x::char list) y::char list. x \<noteq> ''Eve'' \<and> y \<noteq> ''Eve'' \<and> 
  ((Abs :: identity option \<Rightarrow> actor)o Actor_Abs) x = ((Abs :: identity option \<Rightarrow> actor)o Actor_Abs) y 
   \<longrightarrow> x = y)"
by (insert UasI_ActorAbs, simp, clarify, drule_tac x = x in spec, drule_tac x = y in spec,
    subgoal_tac "Actor_Abs x = Actor_Abs y", simp, rule Abs_inj_on, rule Actor_Abs_ran, rule Actor_Abs_ran)

text \<open>Finally all of this allows us to show the last assumption contained in the
   Insider Locale assumption needed for the interpretation of airplane.\<close>
lemma UasI_Actor: "UasI ''Eve'' ''Charly''"
 by (unfold UasI_def, insert Actor_redef, drule meta_spec, erule ssubst, rule UasI_Actor_redef)

interpretation airplane airplane_actors airplane_locations cockpit door cabin global_policy 
               ex_creds ex_locs ex_locs' ex_graph aid_graph aid_graph0 agid_graph 
               local_policies local_policies_four_eyes Airplane_scenario Airplane_in_danger
               Airplane_getting_in_danger0 Airplane_getting_in_danger Air_states Air_Kripke
               Airplane_not_in_danger Airplane_not_in_danger_init Air_tp_states 
               Air_tp_Kripke Safety Security foe_control astate
 by (rule airplane.intro, simp add: tipping_point_def,
     simp add: Insider_def UasI_def tipping_point_def atI_def, 
     insert UasI_Actor, simp add: UasI_def,
     insert cockpit_foe_control', simp add: foe_control_def' cockpit_def',
     rule airplane_actors_def',
    (simp add: airplane_locations_def' cockpit_def' door_def' cabin_def' global_policy_def'
               ex_creds_def' ex_locs_def' ex_locs'_def' ex_graph_def' aid_graph_def' aid_graph0_def' 
               agid_graph_def' local_policies_def' local_policies_four_eyes_def' Airplane_scenario_def'
               Airplane_in_danger_def' Airplane_getting_in_danger0_def' Airplane_getting_in_danger_def'
               Air_states_def'  Air_Kripke_def' Airplane_not_in_danger_def' Airplane_not_in_danger_init_def'
               Air_tp_states_def' Air_tp_Kripke_def' Safety_def' Security_def' 
               foe_control_def' astate_def')+)

end
    
    
