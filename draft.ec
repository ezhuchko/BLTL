pragma Goals : printall.

require import AllCore List Int Bool Distr SmtMap DInterval.



(* MAC *)

type macKey, mac, message.

op mKeygen : {macKey distr | is_lossless mKeygen} as mKeygen_ll. 
op macGen : macKey -> message -> mac.
op macVer : macKey -> mac -> message -> bool. 

(* Correctness of MAC *)
axiom macCorrect : forall k m,  
  k \in mKeygen => macVer k (macGen k m) m = true. 


(* Endorsement Oracle *) 

abstract theory Endorsements.

type pkey, skey, endorsement.
type end_msg = int list.

op endKeygen : end_msg list -> (skey * pkey) distr.
op endGen : skey -> end_msg list -> int -> endorsement.
op endVer : pkey -> endorsement -> end_msg -> int -> bool.

axiom endKeygen_ll : forall xs, is_lossless (endKeygen xs).

axiom endCorrect : forall pk sk i xs m, 
 (sk, pk) \in endKeygen xs => 1 <= i <= size xs => endVer pk (endGen sk xs i) m i = true. 

module type EndOracleT = {
  proc *init(xs : end_msg list) : skey * pkey
  proc genEnd(i : int) : endorsement 
  proc verEnd(e : endorsement, m : end_msg, i : int) : bool
}.

module EndOracle : EndOracleT = {

  var pk : pkey
  var sk : skey
  var xs : end_msg list 

  proc init(xsp : end_msg list) : skey * pkey = {
  (sk, pk) <$ endKeygen xsp;
  xs <- xsp;
  return (sk, pk);
  }

  proc genEnd(i : int) : endorsement = {
    return endGen sk xs i;
  }

  proc verEnd(e : endorsement, m : end_msg, i : int) : bool = {
    return endVer pk e m i;
  }

}. 

module EndCorrect = {

  proc main(ml : end_msg list) = {
    var e : endorsement;
    var b : bool;
    var x : int;

    x <$ [0 .. size ml];
    EndOracle.init(ml);
    e <- EndOracle.genEnd(x);
    b <- EndOracle.verEnd(e, nth witness ml x, x);
    return b;
  }
}.

print dinterE.

(*
lemma EndOracleCorrect &m ml: 
  Pr[ EndCorrect.main(ml) @ &m : res ] = 1%r.  
proof. byphoare (_ : ml = arg ==> _). proc. inline*. wp. 
seq 1 : (0 <= x <= size ml).
rnd. skip. progress.
rnd. skip. progress. 

pose z := size ml{hr}. 
have q : 0 <= z. smt.
smt.

rnd (fun (skpk : skey * pkey) => true). wp.
skip. progress.     
admit.
admit.
admitted.
*)

end Endorsements.


(* Publisher *)

type Time = int.
type digest.

op tdistr : int distr. 
 
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

type tag = int.
type data, cert.
type message_macced = message * mac.

print List.
abbrev (\inl) ['a] (z : 'a) (s : 'a list) : bool = mem s z.

(* Tag-commitment scheme *)

op digestTs : (tag * data) list -> digest.
op certTs : (tag * data) list -> (tag * cert) list.
op verifyTs : digest -> cert -> (tag * data) -> bool.

op certByTag : tag -> (tag * cert) list -> cert.
op dataByTag : tag -> (tag * data) list -> data.

axiom certByTag_prop1 : forall (rl : (tag * data) list) t d (c : cert), 
  (t, d) \inl rl => (t, certByTag t (certTs rl)) \inl (certTs rl).

axiom correctTs : forall (rl : (tag * data) list, d : data, c : cert, t : tag), 
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

op accKey : {acc_pkey distr | is_lossless accKey} as accKey_ll.
op digestQ : acc_pkey -> tag * (message_macced list) -> tag * data. 
op proofQ : acc_pkey -> tag * (message_macced list) -> message_macced -> Proof.
op verifyQ : acc_pkey -> tag * data -> Proof -> message_macced -> bool.

op convertQ : (tag * message_macced) list -> (tag * (message_macced list)) list.

axiom convertQ_prop1 : forall xs t m,  
  (t,m) \inl xs => exists (x : (tag * (message_macced list))), x \inl (convertQ xs) /\ x.`1 = t /\ m \inl x.`2.

op getByTag : tag -> (tag * (message_macced list)) list -> (message_macced list).

axiom convertQ_prop2 : forall xs t m x, 
  (t,m) \inl xs => getByTag t (convertQ xs) = x.

axiom accumCorrect : forall (m : message_macced) (ml : tag * (message_macced list)) pk, 
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

op paramDistr : int -> int -> (int list) list distr.
axiom paramDistr_ll : forall i j, is_lossless (paramDistr i j).

axiom keygen_r : forall xss i j, 
  xss \in paramDistr i j => size xss = i /\ (forall xs, xs \in xss => size xs = j).  (* valid length of xss *)

type bit_string = int.
op H : bit_string -> bit_string. 
op valid_mac : message_macced list -> macKey -> bool.
axiom valid_mac_1 : forall (mm : message_macced) xs k, mm \inl xs => macVer k mm.`2 mm.`1 = true.

clone export Endorsements as E.

type bltl_signature = endorsement * end_msg * Time * Time * int * int * cert * (tag * data) * Proof.
type bltl_sk = acc_pkey * macKey * end_msg list.
type bltl_pk = int * int * int.

(* BLTL Scheme *)    
module BLTLScheme(EndO : EndOracleT, Q : Qt) = {
   
  proc keygen(act_time : int, rounds : int, max_lag : int) : bltl_sk * bltl_pk  = {  
    var xss, hashed_xss : end_msg list;
    var mac_k : macKey;
    var pkQ : acc_pkey;
    var sk : bltl_sk;
    var pk : bltl_pk;
        
    mac_k <$ mKeygen;
    xss <$ paramDistr act_time rounds;  (* sk list r *)
    hashed_xss <- map(fun xs => List.map (fun x => H x) xs) xss; (* pk list M *) 
    EndO.init(hashed_xss);
    pkQ <- Q.init();
    
    sk <- (pkQ, mac_k, xss);
    pk <- (act_time, rounds, max_lag);
    return (sk, pk); 
  }

(* Client *)
  proc sign(m : message, sk : bltl_sk, pk : bltl_pk) : bltl_signature = {
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
    if(pk.`1 <= t < pk.`1 + pk.`2){
      i <- t - pk.`1;
      e <- EndO.genEnd(i); 
      mm <- (m, macGen sk.`2 m); 
      r_i <- nth witness sk.`3 i; 
     
      (* send request to Q *)
      (t', c, st) <@ Q.processQuery(head witness r_i, mm);
    if(t < t' <= t + pk.`3){
      dg <@ P.get(t');
      v <- verifyTs (oget dg) c (digestQ sk.`1 (head witness r_i, st)) /\ mm \in st /\ valid_mac st sk.`2; 
    }
    
    if(v = true){
    l <- t'-t;
    q <- digestQ sk.`1 (head witness r_i, st);
    z <- proofQ sk.`1 (head witness r_i, st) mm; 
    sig <- (e, r_i, i, l, head witness r_i, nth witness r_i l, c, q, z);   
    }
    }

    return sig;
 
  
    }

  proc verify(m : message, sig : bltl_signature, pk : bltl_pk, sk : bltl_sk) : bool = {
    var valid_e, v, v', ver : bool;
    var t, t' : Time;
    var d : digest option;
    
    valid_e <- EndO.verEnd(sig.`1, sig.`2, sig.`3);

    if(0 < sig.`4 <= pk.`3){  (* 0 < l <= L*)
      t <- pk.`1 + sig.`3;   (* t = C + i *)
      t' <- t + sig.`4;        (* t' = t + l *)
    }
 
    if(pk.`1 < t < pk.`1 + pk.`2){  (* C < t < C + E *)
      if(nth witness sig.`2 1 = H sig.`5 /\ nth witness sig.`2  sig.`4 = H sig.`6){
        d <- P.get(t');
        v <- verifyTs (oget d) sig.`7 sig.`8;
        v' <- verifyQ sk.`1 sig.`8 sig.`9 (m, macGen sk.`2 m);
      }
    }

  return valid_e /\ v /\ v'; 
 
  }
    
}.



module BLTLCorrect(A : AdvQ) = {
  module Q = Q(A)
  module BLTL = BLTLScheme(EndOracle, Q)

  proc main(m : message, act_time : int, rounds : int, max_lag : int) : bool = {
    var sk, pk, sig, b;

    (sk, pk) <@ BLTL.keygen(act_time, rounds, max_lag);
    (* properpty about sk and pk: P (sk , pk) *)

    sig <@ BLTL.sign(sk, m);
    b <@ BLTL.verify(pk, sig, m);

    return b;
  }
}.


section.

declare module A : AdvQ.

lemma bltl_keygen : phoare[BLTLScheme(EndOracle, Q(A)).keygen : true (* rounds, max_lag, act_time are all positive *)  ==> EndOracle.pk = EndOracle.pk (* (pkE, skE) \in endKeyGen  *) ] = 1%r.
proof. 

lemma bltl_correctness &m msg : Pr[BLTLCorrect(A).main(msg) @ &m : res ] = 1%r.
proof. 

