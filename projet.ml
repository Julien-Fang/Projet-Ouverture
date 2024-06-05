open Random
open Printf
open Gc


(*Q1.1*)

module ListeInt64 =   

struct

  type t = int64 list (*liste de Int64*)

  let vide() = [] (*liste vide*)

  (*ajoute x à la fin de la liste*)
  let rec insertQueue x l =   
    match l with
    | [] -> [x]
    | h::t -> h::(insertQueue x t)

  (*ajoute x au début de la liste*)
  let insertTete x l = x::l 

  (*supprime le premier élément de la liste*)
  let removeTete l =  
    match l with
    | [] -> []
    | h::t -> t

  (*retourne le premier élément de la liste*)
  let getTete l =   
    match l with
    | [] -> []
    | h::t -> h

end ;;


(*Q1.3*)

(*ajoute des 0 à gauche de la liste ou bien tronque la liste pour qu'elle ait exactement n éléments*)
let rec completion l n =  
  if n = 0 then []
  else
    match l with
    | [] -> false :: (completion l (n - 1)) 
    | h::t -> h :: (completion t (n - 1)) 


(*Q1.2*)

(*décompose un entier en une liste de booléens*)
let decompositionUnEntier x = 
  let signe = Int64.compare x 0L in (*on récupère le signe de x*)
  let rec aux x =
    if ( x = 0L) then
      [false]
    else if ( x = 1L) then
      [true]
    else
      if (Int64.logand x 1L = 0L) then (*on recupère le bit de poids faible*)
        false :: (aux (Int64.shift_right_logical x 1)) (*on décale à droite de 1 bit*)
      else
        true :: (aux (Int64.shift_right_logical x 1)) (*on décale à droite de 1 bit*)
  in 
    if (signe < 0) then (completion (aux x) 63)@[true] (*si x est négatif, alors il s'agit d'un entier sur 64 bits*)
    else (aux x)

(*décompose un grand entier en une liste de booléens*)
let rec decomposition l = 
  match l with
  | [] -> []
  | h::[] -> (decompositionUnEntier h)
  | h::t -> (completion (decompositionUnEntier h) 64) @ (decomposition t) (*on complète la decomposition de h pour qu'elle soit de taille 64*)


(*Q1.4*)

(*compose une liste de booléens en un grand entier*)
let composition l = 
  let rec aux l cpt tmp c res =
    match l with
    | [] -> if (tmp <> 0L) then (ListeInt64.insertQueue tmp res) else res (*si on se trouve a la fin de la liste et que tmp != 0, on l'ajoute à la fin de res. Dans tous les cas, l'appel est fini et on renvoie res*)
    | h::t -> 
      if (c=64) then (aux l 1L 0L 0 (ListeInt64.insertQueue tmp res))
      else
        if ((c=63) && h) then let tmp_neg=(Int64.neg cpt) in (aux t (Int64.mul cpt 2L) (Int64.add tmp_neg tmp) (c+1) res) (*si on se trouve au 63ème bit et que h est vrai, on ajoute tmp_neg à tmp et on multiplie cpt par 2*)
        else if h then (aux t (Int64.mul cpt 2L) (Int64.add cpt tmp) (c+1) res)
        else (aux t (Int64.mul cpt 2L) tmp (c+1) res) (*si h est faux, on multiplie cpt par 2*)
  in aux l 1L 0L 0 (ListeInt64.vide())


(*Q1.5*)

(*renvoie la liste de booléens de x complétée/tronquée à n bits*)
let table x n = (completion (decompositionUnEntier x) n)  


(*Q1.6*)

(*génère un entier aléatoire sur n bits au maximum*)
let genererAleatoire n = 
  let random = (Random.int64 Int64.max_int) in
  if Random.bool () then
    Int64.shift_right_logical random (64-n) (*on génère un int64 positif sur 64 bits, puis un décalage vers la droite de (64-n) bits*)
  else
    Int64.shift_right_logical (Int64.neg random) (64-n) (*on génère un int64 négatif sur 64 bits, puis un décalage vers la droite de (64-n) bits*)

(*génère un grand entier aleatoire sur n bits au maximum*)
let genAlea n = 
  if (n<=64) then [genererAleatoire n] 
  else 
    let l = n/64 in (*nombre d'éléments sur 64 bits*)
    let m = n - l*64 in (*le reste est sur m bits*)
    let rec aux i = 
      if (i=0) then []
      else (genererAleatoire(64))::(aux (i-1))
    in
  let reste = (genererAleatoire m) in
  if (reste <> 0L) then (aux l)@[reste] (*si le reste est à 0, on ne l'ajoute pas*)
  else (aux l)


(*Q2.7*)

(*structure de donnée permettant d'encoder des arbres binaires de décision*)
type arbre_ref = 
| Feuille of bool (*feuille*)
| Noeud of int * arbre_ref ref * arbre_ref ref (*Noeud (profondeur, fils gauche, fils droit)*)


(*Q2.8*)

(*sépare une liste en deux*)
let split l =  
  let rec aux l r1 r2 n = 
    match l with
    | (h::t) -> if (n>0) then (aux t (r1@[h]) r2 (n-1)) else (aux t r1 (r2@[h]) (n-1))
    | _ -> (r1, r2)
  in aux l [] [] ((List.length l)/2) 

(*renvoie la plus petite puissance de 2 supérieure à n*)
let puissanceSup n = 
  let rec aux p =
    if (p >= n) then p
    else aux (p*2)
  in aux 1

(*construit un arbre binaire de décision à partir d'une liste de booléens*)
let cons_arbre l = 
  let length = List.length l in
  let rec aux l n =
    match l with
    | [] -> ref (Feuille false) (*arbre vide*)
    | h :: [] -> ref (Feuille h) (*feuille*)
    | h :: t ->
        let (l1, l2) = split l in (*on sépare la liste en deux*)
        ref (Noeud(n, aux l1 (n + 1), aux l2 (n + 1))) (*crée un noeud avec les deux listes en faisant un appel récursif*)
  in aux (completion l (puissanceSup length)) 1 (*on complète la liste l pour que sa longueur soit une puissance de 2*)


(*Q2.9*)

(*renvoie la liste des feuilles d'un arbre*)
let rec liste_feuilles a = 
  match !a with
  | Feuille b -> [b]
  | Noeud (_, g, d) -> (liste_feuilles g) @ (liste_feuilles d)  (*appel récursif sur les deux fils du noeud*)


(*Q3.10*)

module ListeDejaVus = 

struct
  type t = (int64 list * arbre_ref) list ref (*liste de couple (grand entier, pointeur vers un noeud)*)

  let vide () = ref []

  (*ajoute x à la tête de la liste*)
  let insertTete x l =
    l := x :: !l

  (*recherche un grand entier dans la liste*)
  let rec recherche x l =   
    match !l with
    | [] -> None
    | (n, a) :: t ->
      if n = x then Some (n, a)  (*si on trouve le grand entier, on renvoie le couple*)
      else recherche x (ref t)  (*sinon on continue la recherche*)

end


(*Q3.11*)

(*algorithme élémentaire de compression d’un arbre de décision avec ListeDejaVus*)
let compressionParListe abr =
  let rec aux abr l parent depuisGauche =
    match !abr with
    | Feuille b -> 
      let n = (composition [b]) in (*on calcule le grand entier de la feuille*)
      let couple = (ListeDejaVus.recherche n l) in (*on cherche si le grand entier est présent dans la ListeDejaVus*)
      (match couple with
        | None -> ListeDejaVus.insertTete (n, abr) l; (*ajout des deux uniques pointeurs vers les feuilles True et False dans la liste*)
        | Some (_, a) -> (*le noeud parent pointera vers l'unique feuille True ou False du graphe*)
          match !parent with
          | Noeud (pp, gg, dd) -> 
            if depuisGauche then parent := Noeud(pp, a, dd)
            else parent := Noeud(pp, gg, a)
          | _ -> ())
    | Noeud (p, g, d) -> 
      let liste_bool = (liste_feuilles abr) in (*on calcule la liste_feuilles associé au noeud*)
      let (_, moitie) = (split liste_bool) in (*on recupere la deuxieme moitié de la liste de booléens*)
      if (List.for_all (fun x -> x = false) moitie) then (*on verifie si la deuxième moitié de la liste ne contient que des valeurs false*)
        match !parent with (*on change le pointeur vers son enfant gauche*)
          | Noeud (pp, gg, dd) -> 
            if depuisGauche then 
              begin
                parent := Noeud(pp, g, dd);
                (aux g l parent true); (*on continue le parcours*)
              end
            else 
              begin
                parent := Noeud(pp, gg, g);
                (aux g l parent false) (*on continue le parcours*)
              end
          | _ -> ()
      else
        begin
          let n = (composition liste_bool) in (*on calcule le grand entier associé au noeud*)
          let couple = (ListeDejaVus.recherche n l) in (*on cherche si le grand entier est présent dans la ListeDejaVus*)
          (match couple with
            | None -> (*le grand entier n'est pas dans la ListeDejaVus, on l'ajoute*)
              (ListeDejaVus.insertTete (n, abr) l); 
              (aux g l abr true); 
              (aux d l abr false);
            | Some (_, a) -> (*le grand entier est dans la ListeDejaVus, on change le pointeur vers le noeud depuis le parent*)
              match !parent with
              | Noeud (pp, gg, dd) -> 
                if depuisGauche then parent := Noeud(pp, a, dd)
                else parent := Noeud(pp, gg, a);
              | _ -> ()) 
        end
  in (aux abr (ListeDejaVus.vide()) (ref(Feuille false)) true)


(*Q3.12*)

(*création d'un noeud*)
let dot_noeud f id label =
  fprintf f "  %d [label=\"%s\"];\n" id label

(*création d'une arête entre deux noeuds*)
let dot_link f id_parent id_enfant isTrait =
  let style = if isTrait then "solid" else "dotted" in
  fprintf f "  %d -- %d [style=\"%s\"];\n" id_parent id_enfant style

(*parcours des noeuds de l'arbre*)
let dot_parcours f abr =
  let rec aux abr parcourus cpt =
  match !abr with
  | Feuille b -> 
    if not (List.exists (fun (_, a) -> a == abr) !parcourus) then (*la feuille n'a pas encore été créée*)
      begin
        dot_noeud f !cpt (string_of_bool b); (*on créé la feuille*)
        parcourus := (!cpt, abr)::(!parcourus); (*on ajoute la feuille à la liste des noeuds déjà parcourus*)
        cpt := !cpt + 1; (*on incrémente le pointeur*)
      end
  | Noeud (profondeur, gauche, droite) ->     
    if not (List.exists (fun (_, a) -> a == abr) !parcourus) then (*le noeud n'a pas encore été créé*)
      begin
        dot_noeud f !cpt (string_of_int profondeur); (*on créé le noeud*)
        parcourus := (!cpt, abr)::(!parcourus); (*on ajoute le noeud à la liste des noeuds déjà parcourus*)
        let id = !cpt in (*on retient l'identifiant du noeud pour la création des arêtes*)
        cpt := !cpt + 1;
        aux gauche parcourus cpt; (*on crée tous les noeuds du sous-arbres gauche*)
        aux droite parcourus cpt; (*on crée tous les noeuds du sous-arbres droite*)
        let id_gauche = (*on recherche l'identifiant de l'enfant gauche*)
          match (List.find_opt (fun (_, a) -> a == gauche) !parcourus) with
        | Some (c, _) -> c
        | None -> -1
        in 
        let id_droite = (*on recherche l'identifiant de l'enfant droit*)
          match (List.find_opt (fun (_, a) -> a == droite) !parcourus) with
          | Some (c, _) -> c
          | None -> -1
        in (*creation des arêtes*)
        dot_link f id id_gauche false; 
        dot_link f id id_droite true;
      end
  in (aux abr (ref []) (ref 0))

(*construit un fichier représentant le graphe en langage dot*)
let dot abr fichier =
  let f = open_out fichier in
  fprintf f "graph G {\n";
  dot_parcours f abr;
  fprintf f "}\n";
  close_out f


(*Q4.15*)

module ArbreDejaVus =

struct

  type arbreDV =  
  | Noeud of arbre_ref ref option * arbreDV ref * arbreDV ref (*Noeud (pointeur vers un noeud, fils gauche, fils droit)*)
  | Feuille (* Feuille *)

  let vide() = ref Feuille  (*arbre vide*)

  (*recherche si il existe un pointeur au bout du parcours de la liste de booléens*)
  let rec recherche liste arbre = 
    match (liste, !arbre) with
    | [], Feuille -> None
    | [], Noeud (None, _, _) -> None
    | [], Noeud (Some p, _, _) -> Some p
    | h::t, Feuille -> None
    | h::t, Noeud (_, g, d) -> if h then (recherche t d) else (recherche t g)

  (*insère un pointeur au bout du parcours de la liste de booléens*)
  let rec inserer liste pointeur arbre = 
    match (liste, !arbre) with
    | [], Feuille -> (*on arrive à la fin de la liste et on est sur une feuille*)
      arbre := Noeud(Some pointeur, vide(), vide()); (*on crée un noeud ayant pour étiquette le pointeur*)
    | [], Noeud (p, g, d) -> (*on arrive à la fin de la liste*)
      arbre := Noeud (Some pointeur, g, d) (*l'étiquette du noeud contient maintenant le pointeur*)
    | (h::t, Feuille) -> (*la liste n'est pas finie, mais on arrive à une feuille*)
      arbre := Noeud(None, vide(), vide()); (*on crée un nouveau noeud puis on continue le parcours de la liste*)
      inserer liste pointeur arbre
    | h::t, Noeud (_, g, d) -> 
      if h then inserer t pointeur d
      else inserer t pointeur g

end;;


(*Q4.17*)

(*algorithme élémentaire de compression d’un arbre de décision avec ArbreDejaVus*)
let compressionParArbre abr =
  let rec aux abr l parent depuisGauche =
    match !abr with
    | Feuille b -> 
      let p = (ArbreDejaVus.recherche [b] l) in (*on cherche si la Feuille est présente dans notre ABR*)
      (match p with
        | None -> (ArbreDejaVus.inserer [b] abr l) (*ajout des deux uniques pointeurs vers les feuilles True et False dans la liste*)
        | Some pointeur -> (*le noeud parent pointera vers l'unique feuille True ou False du graphe*)
          match !parent with
          | Noeud (pp, gg, dd) -> 
            if depuisGauche then parent := Noeud(pp, pointeur, dd)
            else parent := Noeud(pp, gg, pointeur)
          | _ -> ())
    | Noeud (p, g, d) -> 
      let liste_bool = (liste_feuilles abr) in (*on calcule la liste_feuilles associé au noeud*)
      let (_, moitie) = (split liste_bool) in
      if (List.for_all (fun x -> x = false) moitie) then (*on verifie si la deuxième moitié de la liste ne contient que des valeurs false*)
        match !parent with (*on change le pointeur vers son enfant gauche*)
          | Noeud (pp, gg, dd) -> 
            if depuisGauche then 
              begin
                parent := Noeud(pp, g, dd);
                (aux g l parent true); (*on continue le parcours*)
              end
            else 
              begin
                parent := Noeud(pp, gg, g);
                (aux g l parent false) (*on continue le parcours*)
              end
          | _ -> ()
      else
        begin      
        let p = (ArbreDejaVus.recherche liste_bool l) in (*on cherche si l'arbre est déjà présent dans notre ABR*)
        (match p with
          | None -> (*l'arbre n'est pas dans notre ABR, on l'ajoute*)
            (ArbreDejaVus.inserer liste_bool abr l); 
            (aux g l abr true); 
            (aux d l abr false);
          | Some pointeur -> (*l'arbre est dans notre ABR, on change le pointeur du noeud vers ce dernier depuis le parent*)
            match !parent with
            | Noeud (pp, gg, dd) -> 
              if depuisGauche then parent := Noeud(pp, pointeur, dd)
              else parent := Noeud(pp, gg, pointeur);
            | _ -> ())
        end
  in (aux abr (ArbreDejaVus.vide()) (ref(Feuille false)) true)


(*Q6.20*)

(*graphe de la comparaison de la vitesse d’exécution*)
let grapheTemps () =
  let f = open_out "graphe_temps.txt" in
  let rec aux i =
    if (i != 1050) then 
    begin
      let temps1 = ref 0.0 in (*temps de compression avec ListeDejaVus*)
      let temps2 = ref 0.0 in (*temps de compression avec ArbreDejaVus*)
      for j = 1 to 10 do
        let n = genAlea i in (*génération d'un grand entier sur i bits*)

        let abr1 = cons_arbre (decomposition n) in 
        let debut1 = Sys.time () in (*heure du debut de la compression*)
        compressionParListe abr1; 
        let fin1 = Sys.time () in   (*heure de fin de la compression*)
        temps1 := !temps1 +. (fin1 -. debut1); (*on ajoute le temps de compression à la somme en faisant l'ecart entre fin1 et debut1*)
      
        let abr2 = cons_arbre (decomposition n) in  
        let debut2 = Sys.time () in (*heure du debut de la compression*)
        compressionParArbre abr2;
        let fin2 = Sys.time () in  (*heure de fin de la compression*)
        temps2 := !temps2 +. (fin2 -. debut2);  (*on ajoute le temps de compression à la somme en faisant l'ecart entre fin2 et debut2*)
      done;
        
      temps1 := !temps1 /. 10.0; (*on fait la moyenne des 10 temps de compressionParListe*)
      temps2 := !temps2 /. 10.0; (*on fait la moyenne des 10 temps de compressionParArbre*)

      fprintf f "%d %f %f\n" i !temps1 !temps2;
      aux (i+1);
    end
  in (aux 1);
  close_out f


(*graphe de l'espace mémoire utilisé*)
let grapheMemoire () =
  let f = open_out "graphe_memoire.txt" in
  let rec aux i =
    if (i != 1050) then  
      begin
        let memoire1 = ref 0 in (*memoire utilisée par l'arbre non compressé*)
        let memoire2 = ref 0 in (*memoire utilisée par l'arbre compressé avec ListeDejaVus*)
        let memoire3 = ref 0 in (*memoire utilisée par l'arbre compressé avec ArbreDejaVus*)
        for j = 1 to 10 do
          let n = genAlea i in

          Gc.full_major (); (*on force le ramasse-miettes*)
          let debut1 = Gc.stat() in (*on mesure la mémoire utilisée au debut*)
          let _ = cons_arbre (decomposition n) in 
          let fin1 = Gc.stat() in (*on mesure la mémoire utilisée à la fin*)
          memoire1 := !memoire1 + (fin1.live_words - debut1.live_words);  (*on ajoute la mémoire utilisée par l'arbre non compressé*)

          Gc.full_major (); (*on force le ramasse-miettes*)
          let debut2 = Gc.stat() in (*on mesure la mémoire utilisée au debut*)
          let abr2 = cons_arbre (decomposition n) in 
          compressionParListe abr2; 
          Gc.full_major ();
          let fin2 = Gc.stat() in (*on mesure la mémoire utilisée à la fin*)
          memoire2 := !memoire2 + (fin2.live_words - debut2.live_words);  (*on ajoute la mémoire utilisée par l'arbre compressé avec ListeDejaVus*)

          Gc.full_major (); (*on force le ramasse-miettes*)
          let debut3 = Gc.stat() in (*on mesure la mémoire utilisée au debut*)
          let abr3 = cons_arbre (decomposition n) in 
          compressionParListe abr3; 
          Gc.full_major ();
          let fin3 = Gc.stat() in (*on mesure la mémoire utilisée à la fin*)
          memoire3 := !memoire3 + (fin3.live_words - debut3.live_words);  (*on ajoute la mémoire utilisée par l'arbre compressé avec ArbreDejaVus*)
        done;

        memoire1 := !memoire1 / 10;  (*on fait la moyenne des 10 mémoires utilisées par l'arbre non compressé*)
        memoire2 := !memoire2 / 10;  (*on fait la moyenne des 10 mémoires utilisées par l'arbre compressé*) 
        memoire3 := !memoire3 / 10;  (*on fait la moyenne des 10 mémoires utilisées par l'arbre compressé*) 

        fprintf f "%d %d %d %d\n" i !memoire1 !memoire2 !memoire3;
        aux (i+1);
      end
  in (aux 1);
  close_out f


(*calcule le nombre de noeuds d'un arbre de décision*)
let nb_noeud abr =
  let rec aux abr parcourus =
    match !abr with
    | Feuille b -> 
      if not (List.exists (fun a -> a == abr) !parcourus) then
        begin
          parcourus := abr::(!parcourus); 
          1
        end
      else 0
    | Noeud (_, g, d) -> 
      if not (List.exists (fun a -> a == abr) !parcourus) then
        begin
          parcourus := abr::(!parcourus); 
          1 + (aux g parcourus) + (aux d parcourus)
        end
      else 0
  in aux abr (ref [])    

(*graphe du taux de compression*)
let grapheCompression () =
  let f = open_out "graphe_compression.txt" in
  let rec aux i =
    if (i != 1050) then 
      begin
        let taux = ref 0.0 in (*taux de compression*)
        for j = 1 to 10 do
          let n = genAlea i in
          let abr = cons_arbre (decomposition n) in 
          let nb_noeud_avant = (nb_noeud abr) in (*nombre de noeud avant la compression*)

          compressionParListe abr;
          let nb_noeud_apres = (nb_noeud abr) in (*nombre de noeud après la compression*)

          taux := !taux +. (float_of_int nb_noeud_apres /. float_of_int nb_noeud_avant);
        done;

        taux := !taux /. 10.0;
        fprintf f "%d %f\n" i !taux ;
        aux (i+1);
      end
  in (aux 1);
  close_out f


(*Q6.20*)

let probabilite_distribution nb_bits =
  let f = open_out "graphe_probabilite.txt" in
  let taille_max = nb_bits in 
  let tab = Array.make (taille_max + 1) 0 in
  let rec aux i =
    if (i != 1000) then 
      begin
        let n = (genAlea nb_bits) in
        let abr = cons_arbre (decomposition n) in 
        compressionParListe abr;
        let taille = (nb_noeud abr) in
        tab.(taille) <- tab.(taille) + 1;
        aux (i+1);
      end
  in let _ = (aux 1) in
  for j = 0 to taille_max do
    if (tab.(j) <> 0) then Printf.fprintf f "%d %d\n" j tab.(j);
  done;
  close_out f



(*Tests*)

let () =
  assert(decomposition [38L] = [false; true; true; false; false; true]);
  assert(decomposition [0L; 68719476736L] = [false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true]);

  assert(completion [false; true; true; false; false; true] 4 = [false; true; true; false]);
  assert(completion [false; true; true; false; false; true] 8 = [false; true; true; false; false; true; false; false]);

  assert(composition [false; true; true; false; false; true] = [38L]);
  assert(composition [false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true] = [0L; 68719476736L]);

  assert (composition (decomposition [38L]) = [38L]);
  assert (composition (decomposition [0L; 68719476736L]) = [0L; 68719476736L]);
  assert (composition (decomposition [-2513L]) = [-2513L]);
  assert (composition (decomposition [-2513L; -5932L; -5893L]) = [-2513L; -5932L; -5893L]);
  assert (composition (decomposition [-534L; 53252L; -6975L; 1L]) = [-534L; 53252L; -6975L; 1L]);

  assert(table 38L 8 = [false; true; true; false; false; true; false; false]);

  Random.self_init ();
  
  assert (liste_feuilles (cons_arbre (decomposition [25899L])) = [true; true; false; true; false; true; false; false; true; false; true; false; false; true; true; false]);

  assert (composition (liste_feuilles (cons_arbre (decomposition [25899L]))) = [25899L]);
  assert (composition (liste_feuilles (cons_arbre (decomposition [0L; 68719476736L]))) = [0L; 68719476736L]);
  assert (composition (liste_feuilles (cons_arbre (decomposition [-2513L]))) = [-2513L]);
  assert (composition (liste_feuilles (cons_arbre (decomposition [-5613L; -3L; -131563L]))) = [-5613L; -3L; -131563L]);
  assert (composition (liste_feuilles (cons_arbre (decomposition [-534L; 53252L; -6975L; 1L]))) = [-534L; 53252L; -6975L; 1L]);
  
  let n = [25899L] in

  let abr = cons_arbre (decomposition n) in
  dot abr "arbre_non_compresse.dot";

  let abr1 = cons_arbre (decomposition n) in
  compressionParListe abr1;
  dot abr1 "arbre_ListeDejaVus.dot";

  let abr2 = cons_arbre (decomposition n) in
  compressionParArbre abr2;
  dot abr2 "arbre_ArbreDejaVus.dot";

  assert (composition (decomposition n) = n);

  (*grapheTemps ();*)
  (*grapheMemoire ();*)
  (*grapheCompression ();*)
  (*probabilite_distribution 3000;*)


(*
ocamlc projet.ml -o projet.exe

dot -Tpng -o arbre_non_compresse.png arbre_non_compresse.dot; dot -Tpng -o arbre_ListeDejaVus.png arbre_ListeDejaVus.dot; dot -Tpng -o arbre_ArbreDejaVus.png arbre_ArbreDejaVus.dot

set title 'Graphe du temps dexecution de la compression en fonction de la taille du grand entier'
set xlabel 'Taille du grand entier (en bits)'
set ylabel 'Temps dexecution (en secondes)'
plot "graphe_temps.txt" using 1:2 title 'ListeDejaVus' with lines
replot "graphe_temps.txt" using 1:3 title 'ArbreDejaVus' with lines

set title 'Graphe de lespace memoire utilise en fonction de la taille du grand entier'
set xlabel 'Taille du grand entier (en bits)'
set ylabel 'Espace memoire utilise (en octet)'
plot "graphe_memoire.txt" using 1:2 title 'Arbre non compresse' with lines
replot "graphe_memoire.txt" using 1:3 title 'ListeDejaVus' with lines
replot "graphe_memoire.txt" using 1:4 title 'ArbreDejaVus' with lines

set title 'Graphe du taux de compression en fonction de la taille du grand entier'
set xlabel 'Taille du grand entier (en bits)'
set ylabel 'Taux de compression'
plot "graphe_compression.txt" using 1:2 title '' with lines

set title 'Distribution de probabilite des tailles des ZDD pour n=2000'
set xlabel 'Taille du ZDD'
set ylabel 'Nombre doccurences'
plot "graphe_probabilite.txt" with boxes
*)