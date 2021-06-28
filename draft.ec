pragma Goals : printall.

require import AllCore List Int Bool Distr SmtMap DInterval.


(* MAC *)

type macKey, mac.
type message = int.

op mKeygen : macKey distr.
axiom mKeygen_ll : is_lossless mKeygen. 
op macGen : macKey -> message -> mac.
op macVer : macKey -> mac -> message -> bool. 

(* Correctness of MAC *)
axiom macCorrect k m:  
  k \in mKeygen => macVer k (macGen k m) m = true. 

(* Endorsement Scheme *)

type end_pkey, end_skey, endorsement.
type end_msg = int list.

op endKeygen : end_msg list -> (end_pkey * end_skey) distr.
op endGen : end_skey -> end_msg list -> int -> endorsement.
op endVer : end_pkey -> endorsement -> end_msg -> int -> bool.

axiom endKeygen_ll xs : is_lossless (endKeygen xs).
axiom endCorrect pk sk i xs m: 
 (pk, sk) \in endKeygen xs => 1 <= i <= size xs => endVer pk (endGen sk xs i) m i = true. 

(* Publisher *)

type Time = int.
type digest.

op tdistr : int distr.
axiom tdistr_ll : is_lossless tdistr. 
 
module P = {
 
  var t : Time 
  var m : (Time, digest) fmap 

  proc init() : unit = {
    var i : Time; 

    i <$ tdistr;
    t <- i;
  }

  proc clock() : Time = {
    return t;
  }  
  
  proc publish(t' : Time, d : digest) : Time = {
    if (t < t'){
      t <- t'; 
      m <- m.[t <- d];
    }
      return t;
   }
  proc get(t : Time) : digest option = {
    return m.[t];
  }
}.

type data, cert.
type tag = int.
type message_macced = message * mac.
abbrev (\inl) ['a] (z : 'a) (s : 'a list) : bool = mem s z.

(* Tag-commitment scheme *)

op digestTs : (tag * data) list -> digest.
op certTs : (tag * data) list -> (tag * cert) list.
op verifyTs : digest -> cert -> (tag * data) -> bool.
op certByTag : tag -> (tag * cert) list -> cert.
op dataByTag : tag -> (tag * data) list -> data.

axiom certByTag_prop1 (rl : (tag * data) list) t d (c : cert): 
  (t, d) \inl rl => (t, certByTag t (certTs rl)) \inl (certTs rl).

axiom correctTs (rl : (tag * data) list, d : data, c : cert, t : tag):
  (t, c) \inl (certTs rl) => verifyTs (digestTs rl) (certByTag t (certTs rl)) (t, (dataByTag t rl)) = true.

module type TS = {
   proc processQuery (ql : (tag * data) list, t' : Time) : Time * (tag * cert) list
}.

module Ts : TS = {

  proc processQuery(ql : (tag * data) list, t' : Time) : Time * (tag * cert) list = {
    var cs : (tag * cert) list; 
    var dg : digest;
    var t : Time;
     
    dg <- digestTs ql;
    t <@ P.publish(t', dg);
    cs <- certTs ql;
    return (t, cs); 
  }
}.


type acc_pkey, Proof.

op accKey : acc_pkey distr.
op digestQ : acc_pkey -> tag * (message_macced list) -> tag * data. 
op proofQ : acc_pkey -> tag * (message_macced list) -> message_macced -> Proof.
op verifyQ : acc_pkey -> tag * data -> Proof -> message_macced -> bool.
op convertQ : (tag * message_macced) list -> (tag * (message_macced list)) list.
op getByTag : tag -> (tag * (message_macced list)) list -> (message_macced list).

axiom accKey_ll : is_lossless accKey.

axiom convertQ_prop1 xs t m: 
  (t,m) \inl xs => exists (x : (tag * (message_macced list))), x \inl (convertQ xs) /\ x.`1 = t /\ m \inl x.`2.

axiom convertQ_prop2 xs t m x:
  (t,m) \inl xs => getByTag t (convertQ xs) = x.

axiom accumCorrect (m : message_macced) (ml : tag * (message_macced list)) pk:
  pk \in accKey => m \inl ml.`2 => verifyQ pk (digestQ pk ml) (proofQ pk ml m) m = true. 


module type AdvQ = {
  proc askForMore (t : tag, m : message_macced) : (tag * message_macced) list
}. 

module type Qt = {
   proc *init() : acc_pkey
   proc processQuery (t : tag, m : message_macced) : Time * cert * message_macced list
}.

module Q (A : AdvQ) : Qt = {

  var pk : acc_pkey

  proc init() : acc_pkey = {
    pk <$ accKey;
    return pk;
  }

  proc processQuery(t : tag, m : message_macced) : Time * cert * message_macced list = {
    var r, r', joined_r : (tag * message_macced) list;
    var final_r : (tag * (message_macced list)) list;
    var digested_r : (tag * data) list;
    var p : Proof; 
    var tm, t', tp : Time;    (* tp : time published *)
    var cs : (tag * cert) list;
    var c : cert;
     
    r <- A.askForMore(t, m);
    (* excludes the event which might happen with negligible probability *)
    r' <- filter (fun (tm : tag * message_macced) => tm.`1 <> t) r; 
    joined_r <- r' ++ [(t, m)];  
    final_r <- convertQ joined_r;
    digested_r <- map (digestQ pk) final_r; 
    
    (* send request to Ts *)
    tm <@ P.clock();
    t' <- tm + 1;
    (tp, cs) <@ Ts.processQuery(digested_r, t'); 
    return (tp, certByTag t cs, getByTag t final_r); (* (time, cert, set) back to user *)
  }
}.


(* Key gen *)

type bit_string = int.

op paramDistr : int -> int -> (int list) list distr.
op H : bit_string -> bit_string. 
op valid_mac : message_macced list -> macKey -> bool.
op hashed_xss : end_msg list -> end_msg list. (* pk list M *) 
 
axiom paramDistr_ll i j: is_lossless (paramDistr i j).

axiom keygen_r xss i j:
  xss \in paramDistr i j => size xss = i /\ (forall xs, xs \in xss => size xs = j).  (* valid length of xss *)

axiom valid_mac_1 (mm : message_macced) xs k:
  mm \inl xs => macVer k mm.`2 mm.`1 = true.

(*
axiom hashed_xss_1 xss:
   forall xs, xs \inl xss =>  . *)

(* BLTL Scheme *)   

type bltl_signature = endorsement * end_msg * Time * Time * int * int * cert * (tag * data) * Proof * mac.
type bltl_sk = macKey * end_skey * end_msg list * acc_pkey * int * int * int.
type bltl_pk = end_pkey * int * int * int * acc_pkey.

 
module BLTLScheme(Q : Qt) = {
   
  proc keygen(act_time : int, rounds : int, max_lag : int) : bltl_sk * bltl_pk = {  
    var xss: end_msg list;
    var mac_k : macKey;
    var pkQ : acc_pkey;
    var pk_e : end_pkey;
    var sk_e : end_skey;
        
    mac_k <$ mKeygen;
    xss <$ paramDistr act_time rounds;  (* sk list r *)
    (pk_e, sk_e) <$ endKeygen(hashed_xss xss);
    pkQ <- Q.init();
    
    return ((mac_k, sk_e, xss, pkQ, act_time, rounds, max_lag), (pk_e, act_time, rounds, max_lag, pkQ)); 
  }

(* Client *)
  proc sign(sk : bltl_sk, m : message) : bltl_signature = {
    var t, i, t', l : Time;
    var e : endorsement;
    var mm : message_macced;
    var c : cert;
    var st : message_macced list;
    var dg : digest option;
    var v : bool;
    var r_i : end_msg; 
    var q : tag * data;
    var z : Proof;
    var sig : bltl_signature;
    
    t <- P.clock();
    if(sk.`5 <= t < sk.`5 + sk.`6){ (* C <= t < C + E *)
      i <- t - sk.`5; (* i = t - C *)
      e <- endGen sk.`2 (hashed_xss (sk.`3)) i; 
      mm <- (H m, macGen sk.`1 (H m)); 
      r_i <- nth witness sk.`3 i; 
     
      (* send request to Q *)
      (t', c, st) <@ Q.processQuery(head witness r_i, mm);
    if(t < t' <= t + sk.`7){  (* t < t' <= t + L *)
      dg <@ P.get(t');
      v <- verifyTs (oget dg) c (digestQ sk.`4 (head witness r_i, st)) /\ mm \in st /\ valid_mac st sk.`1; 
    }
    
    if(v = true){
      l <- t'- t;
      q <- digestQ sk.`4 (head witness r_i, st);
      z <- proofQ sk.`4 (head witness r_i, st) mm; 
      sig <- (e, r_i, i, l, head witness r_i, nth witness r_i l, c, q, z, mm.`2);   
    }
    }

    return sig;
  
    }

  proc verify(pk : bltl_pk, sig : bltl_signature, m : message) : bool = {
    var valid_e, v, v', ver : bool;
    var t, t' : Time;
    var d : digest option;
    
    valid_e <- endVer pk.`1 sig.`1 sig.`2 sig.`3;

    if(0 < sig.`4 <= pk.`3){  (* 0 < l <= L*)
      t <- pk.`2 + sig.`3;   (* t = C + i *)
      t' <- t + sig.`4;        (* t' = t + l *)
    }
 
    if(pk.`2 < t < pk.`2 + pk.`3){  (* C < t < C + E *)
      if(nth witness sig.`2 1 = H sig.`5 /\ nth witness sig.`2  sig.`4 = H sig.`6){  (* w_0 == H(a) /\ w_l == H(r) *)
        d <- P.get(t');
        v <- verifyTs (oget d) sig.`7 sig.`8; (* V(d,c,(a,q)) *)
        v' <- verifyQ pk.`5 sig.`8 sig.`9 (H m, sig.`10); (* V(q,z,h(m)||p) *)
      }
    }

  return valid_e /\ v /\ v'; 
 
  }
    
}.


module BLTLCorrect(A : AdvQ) = {
  module Q = Q(A)
  module BLTL = BLTLScheme(Q)

  proc main(m : message, act_time : int, rounds : int, max_lag : int) : bool = {
    var sk, pk, sig, b;

    (sk, pk) <@ BLTL.keygen(act_time, rounds, max_lag);
    (* property about sk and pk: P (sk , pk) *)

    sig <@ BLTL.sign(sk, m);
    b <@ BLTL.verify(pk, sig, m);

    return b;
  }
}.


section.

(* define adversary *)
declare module A : AdvQ.


lemma bltl_keygen : 
phoare[BLTLScheme(Q(A)).keygen : 0 <= rounds /\ 0 <= max_lag /\ 0 <= act_time ==> (res.`2.`1, res.`1.`2) \in endKeygen (hashed_xss (res.`1.`3)) /\ res.`1.`1 \in mKeygen /\ res.`1.`4 = res.`2.`5 /\ res.`1.`4 \in accKey] = 1%r.
proof. 
proc. simplify. wp. progress. inline*.

seq 1 : (mac_k \in mKeygen /\ 0 <= rounds /\ 0 <= max_lag /\ 0 <= act_time). rnd. skip. 
progress. rnd. skip. progress. rewrite H H0 H1. simplify. 
rewrite eq1_mu. apply mKeygen_ll. progress. trivial.

seq 1 : (mac_k \in mKeygen /\ 0 <= rounds /\ 0 <= max_lag /\ 0 <= act_time /\ xss \in paramDistr act_time rounds). rnd. skip.
progress. rnd. skip. progress. rewrite H H0 H1 H2. simplify. 
rewrite eq1_mu. apply paramDistr_ll. progress. trivial.
 
seq 1 : (mac_k \in mKeygen /\ 0 <= rounds /\ 0 <= max_lag /\ 0 <= act_time /\ xss \in paramDistr act_time rounds /\ (pk_e, sk_e) \in endKeygen (hashed_xss xss)). 

rnd. skip. progress. rnd (fun (pe : end_pkey * end_skey) => (pe.`1, pe.`2) \in endKeygen (hashed_xss xss)). skip. progress. 
rewrite eq1_mu. apply endKeygen_ll. progress. 

have ->: (x.`1, x.`2) = x.  admit. apply H4. auto. 

seq 1 : ((mac_k \in mKeygen) /\ 0 <= rounds /\ 0 <= max_lag /\ 0 <= act_time /\ (xss \in paramDistr act_time rounds) /\ ((pk_e, sk_e) \in endKeygen (hashed_xss xss)) /\ Q.pk \in accKey). rnd. progress. rnd. skip. progress. rewrite eq1_mu. apply accKey_ll. progress. trivial.

seq 1 : ((mac_k \in mKeygen) /\ 0 <= rounds /\ 0 <= max_lag /\ 0 <= act_time /\ (xss \in paramDistr act_time rounds) /\ ((pk_e, sk_e) \in endKeygen (hashed_xss xss)) /\ Q.pk \in accKey /\ pkQ = Q.pk). progress. wp. skip. progress. skip. progress. 

trivial. wp. skip. progress. 



lemma bltl_sign :
phoare[BLTLScheme(Q(A)).sign : (* sk <- BLTL.keygen *)] = 1%r.
proof.


lemma bltl_verify :
phoare[BLTLScheme(Q(A)).verify : (* pk <- BLTL.keygen, sig <- BLTL.sign *)] = 1%r.
proof.
