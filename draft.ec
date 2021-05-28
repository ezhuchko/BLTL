pragma Goals : printall.

require import AllCore List Int Bool Distr SmtMap DInterval.



(* MAC *)

type macKey, mac, message.

op mKeygen : macKey distr. 
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

    x <$ [1 .. size ml];
    EndOracle.init(ml);
    e <- EndOracle.genEnd(x);
    b <- EndOracle.verEnd(e, nth witness ml x, x);
    return b;
  }
}.

print Distr.
print dinterE.


lemma EndOracleCorrect &m ml: 
  Pr[ EndCorrect.main(ml) @ &m : res ] = 1%r.  
proof. byphoare => //. proc. inline*. wp. 
seq 1 : (1 <= x <= size ml).
rnd. skip. progress.
rnd. skip. progress.
rewrite dinterE. simplify. admit.
rnd (fun (skpk : skey * pkey) => true). wp.
skip. progress.   
admit. admit. admit. auto.
qed. 

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

type tag = int. (* to do : clone instead *)
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


module Ts  = {

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
op digestQ : acc_pkey -> (tag * (message_macced list)) list -> (tag * data) list. 
op proofQ : acc_pkey -> (tag * (message_macced list)) list -> message_macced -> Proof.
op verifyQ : acc_pkey -> (tag * data) list -> Proof -> message_macced -> bool.

op convertQ : (tag * message_macced) list -> (tag * (message_macced list)) list.
axiom convertQ_prop1 : forall xs t m,  
  (t,m) \inl xs => exists (x : (tag * (message_macced list))), x \inl (convertQ xs) /\ x.`1 = t /\ m \inl x.`2.

op getByTag : tag -> (tag * (message_macced list)) list -> (message_macced list).

axiom convertQ_prop2 : forall (xs : (tag * message_macced) list) t m (x : message_macced list), 
  (t,m) \inl xs => getByTag t (convertQ xs) = x.

axiom accumCorrect : forall (m : message_macced) (t : tag) (ml : message_macced list) (pk : acc_pkey) (xs : (tag * message_macced list) list), 
  pk \in accKey => (t, ml) \inl xs => verifyQ pk (digestQ pk xs) (proofQ pk xs m) m = true. 


module type AdvQ = {
  proc askForMore (t : tag, m : message_macced) : (tag * message_macced) list
}. 

module type Qt = {
   proc *init() : unit
   proc processQuery (t : tag, m : message_macced) : Time * cert * message_macced list
}.

module Q (A : AdvQ) = {

  var pk : acc_pkey

  proc init() : unit = {
    pk <$ accKey;
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
    joined_r <- r ++ [(t, m)];  
    final_r <- convertQ joined_r;
    digested_r <- digestQ pk final_r; 
    
    (* send request to Ts *)
    tm <@ P.clock();
    t' <- tm + 1;
    (tp, cs) <@ Ts.processQuery(digested_r, t'); 
    return (tp, certByTag t cs, getByTag t final_r); (* (time, cert, set) back to user *)
  }
}.


(* Key gen *)

op paramDistr : int -> int -> (int list) list distr.

axiom keygen_r : forall xss i j, 
  xss \in paramDistr i j => size xss = i /\ (forall xs, xs \in xss => size xs = j).  (* valid length of xss *)

type bit_string = int.
op H : bit_string -> bit_string. 

clone export Endorsements as E.

(* BLTL Scheme *)    
module BLTLScheme(EndO : EndOracleT, Q : Qt) = {

  var act_time : int
  var rounds : int
  var max_lag : int
   
  proc keygen(i : int, j : int, act_time : int, rounds : int, max_lag : int) = {  
    var xss, hashed_xss : end_msg list;
    var mac_k : macKey;
        
    mac_k <$ mKeygen;
    xss <$ paramDistr i j;  (* sk list r *)
    hashed_xss <- map(fun xs => List.map (fun x => H x) xs) xss; (* pk list M *) 
    EndO.init(hashed_xss);
    Q.init();
    return (mac_k, xss);
  }

(* Client *)
  proc sign(m : message, mac_k : macKey, xss : end_msg list) = {
    var t, i, t' : Time;
    var e : endorsement;
    var mm : message_macced;
    var c : cert;
    var st : message_macced list;
    var dg : digest option;
    var v : bool;
    var r_i : end_msg; 
 
    while (act_time <= t <= act_time + rounds){
      t <@ P.clock();  
      i <- t - act_time;
    }

    e <- EndO.genEnd(i); 
    mm <- (m, macGen mac_k m); 
    r_i <- nth witness xss i; 
  
    (* send request to Q *)
    (t', c, st) <@ Q.processQuery(head witness r_i, mm);
    while (t < t' <= t + max_lag){
      dg <@ P.get(t');
      v <- verifyTs dg c (head witness r_i, digestQ pk (head witness r_i, st)) /\ mm \in st; 
    }

    (* for every x \in st, there is a valid mac *)
    }
   (* return (e, nth witness hashed_xss i, i, t'-t, nth witness r_i t'-t, c, .., .., macGen mac_k m )*) 

(*  proc verify(m : message (* signature *)) = {
    var valid_e : bool;
    
    valid_e <- EndO.ver(e, m_i, i);
    }
*)

}.
