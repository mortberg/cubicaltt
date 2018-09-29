-- Specialized evaluation function for closed well-typed terms
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, BangPatterns #-}
module FastEval where

import qualified Data.Map as Map
import Data.List
import Data.Maybe (fromMaybe,fromJust)
import qualified Data.Set as Set

import Connections
import CTT hiding (sub,subs,upd,upds,updsTele,emptyEnv,defWhere)

import Debug.Trace

-----------------------------------------------------------------------
-- Lookup functions

-- look :: String -> Env -> Val
-- look x (Env (Upd y rho,v:vs,fs,os)) | x == y = v
--                                     | otherwise = look x (Env (rho,vs,fs,os))
-- look x r@(Env (Def _ decls rho,vs,fs,Nameless os)) = case lookup x decls of
--   Just (_,t) -> eval r t
--   Nothing    -> look x (Env (rho,vs,fs,Nameless os))
-- look x (Env (Sub _ rho,vs,_:fs,os)) = look x (Env (rho,vs,fs,os))
-- look x (Env (Empty,_,_,_)) = error $ "look: not found " ++ show x

-- type VarEnv = (Map.Map Ident Val,Map.Map Ident Ter)

-- type NameEnv = Map.Map Name Formula

-- data FastEnv = E (Map.Map Ident Ter) (Map.Map Ident Val) (Map.Map Name Formula)

-- data Ctxt = Empty
--           | Upd Ident Ctxt
--           | Sub Name Ctxt
--           | Def Loc [Decl] Ctxt

-- newtype Env = Env (Ctxt,[Val],[Formula],Nameless (Set Ident))

toFastEnv :: Env -> FastEnv
toFastEnv (Env (Empty,_,_,_)) = emptyEnv
toFastEnv (Env (Upd x ctxt,v:vs,fs,os)) =
  upd (x,v) (toFastEnv (Env (ctxt,vs,fs,os)))
toFastEnv (Env (Sub n ctxt,vs,f:fs,os)) =
  sub (n,f) (toFastEnv (Env (ctxt,vs,fs,os)))
toFastEnv (Env (Def _ ds ctxt,vs,fs,os)) =
  decls ds (toFastEnv (Env (ctxt,vs,fs,os)))

instance Nominal (Map.Map Ident Val) where
  occurs x xs = occurs x (Map.elems xs)
  act b xs iphi = Map.map (\x -> act b x iphi) xs
  swap xs ij = Map.map (\x -> swap x ij) xs

instance Nominal (Map.Map Name Formula) where
  occurs x xs = occurs x (Map.elems xs)
  act b xs iphi = Map.map (\x -> act b x iphi) xs
  swap xs ij = Map.map (\x -> swap x ij) xs

emptyEnv :: FastEnv
emptyEnv = E Map.empty Map.empty Map.empty

sub :: (Name,Formula) -> FastEnv -> FastEnv
sub (i,phi) (E ds vs fs) = E ds vs (Map.insert i phi fs)

subs :: [(Name,Formula)] -> FastEnv -> FastEnv
subs iphis rho = foldl (flip sub) rho iphis

upd :: (Ident,Val) -> FastEnv -> FastEnv
upd (x,v) (E ds vs fs) = E ds (Map.insert x v vs) fs

upds :: [(Ident,Val)] -> FastEnv -> FastEnv
upds xus rho = foldl (flip upd) rho xus

updsTele :: Tele -> [Val] -> FastEnv -> FastEnv
updsTele tele vs = upds (zip (map fst tele) vs)

decl :: Decl -> FastEnv -> FastEnv
decl (x,(_,d)) (E ds vs fs) = E (Map.insert x d ds) vs fs

decls :: [Decl] -> FastEnv -> FastEnv
decls ds rho = foldl (flip decl) rho ds

-- Only support non-mutual Decls
defWhere :: Decls -> FastEnv -> FastEnv
defWhere (MutualDecls m [(x,(_,d))]) (E ds vs fs) =
  E (Map.insert x d ds) vs fs

look :: Ident -> FastEnv -> Val
look x env@(E ds vs _) = case Map.lookup x vs of
  Just v -> v
  Nothing -> case Map.lookup x ds of
    Just t -> eval env t
    Nothing -> error "look"

lookName :: Name -> FastEnv -> Formula
lookName x (E _ _ fs) = case Map.lookup x fs of
  Just phi -> phi
  Nothing -> error "lookName"

-- lookName :: Name -> Env -> Formula
-- lookName i (Env (Upd _ rho,v:vs,fs,os)) = lookName i (Env (rho,vs,fs,os))
-- lookName i (Env (Def _ _ rho,vs,fs,os)) = lookName i (Env (rho,vs,fs,os))
-- lookName i (Env (Sub j rho,vs,phi:fs,os)) | i == j    = phi
--                                           | otherwise = lookName i (Env (rho,vs,fs,os))
-- lookName i _ = error $ "lookName: not found " ++ show i


-----------------------------------------------------------------------
-- Nominal instances

-- instance Nominal Ctxt where
--   occurs _ _ = False
--   act b e _   = e
--   swap e _  = e

instance Nominal FastEnv where
  occurs x (E _ vs fs) = occurs x (vs,fs)
  act b (E ds vs fs) iphi = E ds (act b vs iphi) (act b fs iphi)
  swap (E ds vs fs) ij = E ds (swap vs ij) (swap fs ij)

instance Nominal Val where
  occurs x v = case v of
    VU                      -> False
--    Ter _ e                 -> occurs x e
    FastTer _ e             -> occurs x e
    VPi u v                 -> occurs x (u,v)
    VPathP a v0 v1          -> occurs x [a,v0,v1]
    VPLam i v               -> if x == i then False else occurs x v
    VSigma u v              -> occurs x (u,v)
    VPair u v               -> occurs x (u,v)
    VFst u                  -> occurs x u
    VSnd u                  -> occurs x u
    VCon _ vs               -> occurs x vs
    VPCon _ a vs phis       -> occurs x (a,vs,phis)
    VHComp i a u ts         -> if x == i then occurs x (a,u) else occurs x (a,u,ts)
    VComp i a u ts          -> if x == i then occurs x u else occurs x (a,u,ts)    
    VTrans a phi u          -> occurs x (a,phi,u)
    VVar _ v                -> occurs x v
    VOpaque _ v             -> occurs x v
    VApp u v                -> occurs x (u,v)
    VLam _ u v              -> occurs x (u,v)
    VAppFormula u phi       -> occurs x (u,phi)
    VSplit u v              -> occurs x (u,v)
    VGlue a ts              -> occurs x (a,ts)
    VGlueElem a ts          -> occurs x (a,ts)
    VUnGlueElem a b ts      -> occurs x (a,b,ts)
    VHCompU i a ts          -> if x == i then occurs x a else occurs x (a,ts)
    VUnGlueElemU a b (i,es) -> if x == i then occurs x (a,b) else occurs x (a,b,es)

  act b u (i, phi)
    | b = case u of
         VU           -> VU
--         Ter t e      -> Ter t (act b e (i,phi))
         FastTer t e  -> FastTer t (act b e (i,phi))
         VPi a f      -> VPi (act b a (i,phi)) (act b f (i,phi))
         VPathP a u v -> VPathP (act b a (i,phi)) (act b u (i,phi)) (act b v (i,phi))
         VPLam j v | j == i -> u
                   | otherwise -> VPLam j (act b v (i,phi))
         VSigma a f              -> VSigma (act b a (i,phi)) (act b f (i,phi))
         VPair u v               -> VPair (act b u (i,phi)) (act b v (i,phi))
         VFst u                  -> fstVal (act b u (i,phi))
         VSnd u                  -> sndVal (act b u (i,phi))
         VCon c vs               -> VCon c (act b vs (i,phi))
         VPCon c a vs phis       -> pcon c (act b a (i,phi)) (act b vs (i,phi)) (act b phis (i,phi))
         VHComp j a u us | j == i -> hcomp j (act b a (i,phi)) (act b u (i,phi)) us
                         | otherwise -> hcomp j (act b a (i,phi)) (act b u (i,phi)) (act b us (i,phi))
         VComp j a u us | j == i -> comp j a (act b u (i,phi)) us
                        | otherwise -> comp j (act b a (i,phi)) (act b u (i,phi)) (act b us (i,phi))
         VTrans a psi u          -> trans (act b a (i,phi)) (act b psi (i,phi)) (act b u (i,phi))
         VVar x v                -> VVar x (act b v (i,phi))
         VOpaque x v             -> VOpaque x (act b v (i,phi))
         VAppFormula u psi       -> act b u (i,phi) @@ act b psi (i,phi)
         VApp u v                -> app (act b u (i,phi)) (act b v (i,phi))
         VLam x t u              -> VLam x (act b t (i,phi)) (act b u (i,phi))
         VSplit u v              -> app (act b u (i,phi)) (act b v (i,phi))
         VGlue a ts              -> glue (act b a (i,phi)) (act b ts (i,phi))
         VGlueElem a ts          -> glueElem (act b a (i,phi)) (act b ts (i,phi))
         VUnGlueElem a bb ts     -> unglue (act b a (i,phi)) (act b bb (i,phi)) (act b ts (i,phi))
         VUnGlueElemU a bb (j,es)
           | j == i -> unglueU (act b a (i,phi)) (act b bb (i,phi)) (j,es)
           | otherwise -> unglueU (act b a (i,phi)) (act b bb (i,phi)) (j,act b es (i,phi))
         VHCompU j a ts | j == i -> hcompUniv j (act b a (i,phi)) ts
                        | otherwise -> hcompUniv j (act b a (i,phi)) (act b ts (i,phi))
    | otherwise = case u of
         VU           -> VU
--         Ter t e      -> Ter t (act b e (i,phi))
         FastTer t e  -> FastTer t (act b e (i,phi))
         VPi a f      -> VPi (act b a (i,phi)) (act b f (i,phi))
         VPathP a u v -> VPathP (act b a (i,phi)) (act b u (i,phi)) (act b v (i,phi))
         VPLam j v | j == i -> u
                   | otherwise -> VPLam j (act b v (i,phi))
         VSigma a f              -> VSigma (act b a (i,phi)) (act b f (i,phi))
         VPair u v               -> VPair (act b u (i,phi)) (act b v (i,phi))
         VFst u                  -> VFst (act b u (i,phi))
         VSnd u                  -> VSnd (act b u (i,phi))
         VCon c vs               -> VCon c (act b vs (i,phi))
         VPCon c a vs phis       -> VPCon c (act b a (i,phi)) (act b vs (i,phi)) (act b phis (i,phi))
         VHComp j a u us | j == i -> VHComp j (act b a (i,phi)) (act b u (i,phi)) us
                         | otherwise -> VHComp j (act b a (i,phi)) (act b u (i,phi)) (act b us (i,phi))
         VComp j a u us | j == i -> VComp j a (act b u (i,phi)) us
                        | otherwise -> VComp j (act b a (i,phi)) (act b u (i,phi)) (act b us (i,phi))
         VTrans a psi u          -> VTrans (act b a (i,phi)) (act b psi (i,phi)) (act b u (i,phi))
         VVar x v                -> VVar x (act b v (i,phi))
         VOpaque x v             -> VOpaque x (act b v (i,phi))
         VAppFormula u psi       -> VAppFormula (act b u (i,phi)) (act b psi (i,phi))
         VApp u v                -> VApp (act b u (i,phi)) (act b v (i,phi))
         VLam x t u              -> VLam x (act b t (i,phi)) (act b u (i,phi))
         VSplit u v              -> VSplit (act b u (i,phi)) (act b v (i,phi))
         VGlue a ts              -> VGlue (act b a (i,phi)) (act b ts (i,phi))
         VGlueElem a ts          -> VGlueElem (act b a (i,phi)) (act b ts (i,phi))
         VUnGlueElem a bb ts     -> VUnGlueElem (act b a (i,phi)) (act b bb (i,phi)) (act b ts (i,phi))
         VUnGlueElemU a bb (j,es)
           | j == i -> VUnGlueElemU (act b a (i,phi)) (act b bb (i,phi)) (j,es)
           | otherwise -> VUnGlueElemU (act b a (i,phi)) (act b bb (i,phi)) (j,act b es (i,phi))
         VHCompU j a ts | j == i -> VHCompU j (act b a (i,phi)) ts
                        | otherwise -> VHCompU j (act b a (i,phi)) (act b ts (i,phi))
  -- This increases efficiency as it won't trigger computation.
  swap u ij@(i,j)
    | not (i `occurs` u) = u
    | otherwise = swapVal u ij
    where
      swapVal u ij = case u of
         VU                      -> VU
--         Ter t e                 -> Ter t (swap e ij)
         FastTer t e             -> FastTer t (swap e ij)         
         VPi a f                 -> VPi (swapVal a ij) (swapVal f ij)
         VPathP a u v            -> VPathP (swapVal a ij) (swapVal u ij) (swapVal v ij)
         VPLam k v               ->
           if k == i then VPLam k v else VPLam k (swap v ij)
         VSigma a f              -> VSigma (swapVal a ij) (swapVal f ij)
         VPair u v               -> VPair (swapVal u ij) (swapVal v ij)
         VFst u                  -> VFst (swapVal u ij)
         VSnd u                  -> VSnd (swapVal u ij)
         VCon c vs               -> VCon c (swap vs ij)
         VPCon c a vs phis       -> VPCon c (swapVal a ij) (swap vs ij) (swap phis ij)
         VHComp k a u us         ->
           if k == i
              then VHComp j (swapVal a ij) (swapVal u ij) us
              else VHComp k (swapVal a ij) (swapVal u ij) (swap us ij)
         VComp k a u us          ->
           if k == i
              then VComp j a (swapVal u ij) us
              else VComp k (swap a ij) (swapVal u ij) (swap us ij)
         VTrans a phi u          -> VTrans (swapVal a ij) (swap phi ij) (swapVal u ij)
         VVar x v                -> VVar x (swapVal v ij)
         VOpaque x v             -> VOpaque x (swapVal v ij)
         VAppFormula u psi       -> VAppFormula (swapVal u ij) (swap psi ij)
         VApp u v                -> VApp (swapVal u ij) (swapVal v ij)
         VLam x u v              -> VLam x (swapVal u ij) (swapVal v ij)
         VSplit u v              -> VSplit (swapVal u ij) (swapVal v ij)
         VGlue a ts              -> VGlue (swapVal a ij) (swap ts ij)
         VGlueElem a ts          -> VGlueElem (swapVal a ij) (swap ts ij)
         VUnGlueElem a b ts      -> VUnGlueElem (swapVal a ij) (swapVal b ij) (swap ts ij)
         VUnGlueElemU a b (k,es)     ->
           if k == i
              then VUnGlueElemU (swapVal a ij) (swapVal b ij) (j,es)
              else VUnGlueElemU (swapVal a ij) (swapVal b ij) (k,swap es ij)
         VHCompU k a ts          ->
           if k == i
              then VHCompU j (swapVal a ij) ts
              else VHCompU k (swapVal a ij) (swap ts ij)

-----------------------------------------------------------------------
-- The evaluator
eval :: FastEnv -> Ter -> Val
eval rho v = case v of
  U                   -> VU
  App r s             -> app (eval rho r) (eval rho s)
  Var i               -> look i rho
  Pi t@(Lam _ a _)    -> VPi (eval rho a) (eval rho t)
  Sigma t@(Lam _ a _) -> VSigma (eval rho a) (eval rho t)
  Pair a b            -> VPair (eval rho a) (eval rho b)
  Fst a               -> fstVal (eval rho a)
  Snd a               -> sndVal (eval rho a)
  Where t decls       -> eval (defWhere decls rho) t
  Con name ts         -> VCon name (map (eval rho) ts)
  PCon name a ts phis ->
    pcon name (eval rho a) (map (eval rho) ts) (map (evalFormula rho) phis)
  Lam{}               -> FastTer v rho
  Split{}             -> FastTer v rho
  Sum{}               -> FastTer v rho
  HSum{}              -> FastTer v rho
  Undef{}             -> FastTer v rho
  Hole{}              -> FastTer v rho
  PathP a e0 e1       -> VPathP (eval rho a) (eval rho e0) (eval rho e1)
  PLam{}              -> FastTer v rho
  AppFormula e phi    -> eval rho e @@ evalFormula rho phi
  HComp i a t0 ts       ->
    hcomp i (eval rho a) (eval rho t0) (evalSystem (sub (i,Atom i) rho) ts)
  HFill i a t0 ts       ->
    VPLam i $ hfill i (eval rho a) (eval rho t0) (evalSystem (sub (i,Atom i) rho) ts)
  Trans (PLam i a) phi t ->
    let j = fresh ()
    in trans (VPLam j (eval (sub (i,Atom j) rho) a)) (evalFormula rho phi) (eval rho t)
  Trans a phi t       ->
    let j = fresh ()
    in trans (VPLam j (eval (sub (j,Atom j) rho) (AppFormula a (Atom j)))) (evalFormula rho phi) (eval rho t)
  Comp i a t0 ts        ->
    comp i (eval (sub (i,Atom i) rho) a) (eval rho t0) (evalSystem (sub (i,Atom i) rho) ts)
  Fill i a t0 ts        ->
    VPLam i $ fill i (eval (sub (i,Atom i) rho) a) (eval rho t0) (evalSystem (sub (i,Atom i) rho) ts)
  Glue a ts           -> glue (eval rho a) (evalSystem rho ts)
  GlueElem a ts       -> glueElem (eval rho a) (evalSystem rho ts)
  UnGlueElem v a ts   -> unglue (eval rho v) (eval rho a) (evalSystem rho ts)
  _                   -> error $ "Cannot evaluate " ++ show (showTer v)

evalFormula :: FastEnv -> Formula -> Formula
evalFormula rho phi = case phi of
  Atom i         -> lookName i rho
  NegAtom i      -> negFormula (lookName i rho)
  phi1 :/\: phi2 -> evalFormula rho phi1 `andFormula` evalFormula rho phi2
  phi1 :\/: phi2 -> evalFormula rho phi1 `orFormula` evalFormula rho phi2
  _              -> phi

evalSystem :: FastEnv -> System Ter -> System Val
evalSystem rho (Sys ts) =
  let out = concat [ let betas = meetss [ invFormula (lookName i rho) d
                                        | (i,d) <- alpha ]
                     in [ (beta,eval (rho `face` beta) talpha) | beta <- betas ]
                   | (alpha,talpha) <- ts ]
  in mkSystem out

app :: Val -> Val -> Val
app u v = case (u,v) of
  (FastTer (Lam "_" _ t) e,_) -> eval e t -- Treat dummy lambda specially
  (FastTer (Lam x _ t) e,_) -> eval (upd (x,v) e) t
  (FastTer (Split _ _ _ nvs) e,VCon c vs) -> case lookupBranch c nvs of
    Just (OBranch _ xs t) -> eval (upds (zip xs vs) e) t
    _     -> error $ "app: missing case in split for " ++ c
  (FastTer (Split _ _ _ nvs) e,VPCon c _ us phis) -> case lookupBranch c nvs of
    Just (PBranch _ xs is t) -> eval (subs (zip is phis) (upds (zip xs us) e)) t
    _ -> error $ "app: missing case in split for " ++ c
  (FastTer (Split _ _ ty _) e,VHComp j a w ws) -> case eval e ty of
    VPi _ f -> let w'  = app u w
                   ws' = mapWithKey (\alpha -> app (u `face` alpha)) ws
               in if isNonDep f
                     then hcomp j (app f (VVar "impossible" VU)) w' ws'
                     else comp j (app f (hfill j a w ws)) w' ws'
    _ -> error $ "app: Split annotation not a Pi type " ++ show (showVal u)
  (FastTer Split{} _,_) -> VSplit u v
  (VTrans (VPLam i (VPi a f)) phi u0, v)
      | isNonDep f -> trans (VPLam i (app f (VVar "impossible" VU))) phi (app u0 (transNeg i a phi v))
      | otherwise ->
        let w = transFillNeg i a phi v
            w0 = transNeg i a phi v  -- w0 = w `face` (j ~> 0)
        in trans (VPLam i (app f w)) phi (app u0 w0)
  (VHComp i (VPi a f) u0 us, v) ->
    hcomp i (app f v) (app u0 v)
            (mapWithKey (\al ual -> app ual (v `face` al)) us)
  (VComp j (VPi a f) li0 ts,vi1) ->
    let v       = transFillNeg j a (Dir Zero) vi1
        vi0     = transNeg j a (Dir Zero) vi1
    in if isNonDep f
          then comp j (app f (VVar "impossible" VU)) (app li0 vi0) (intersectionWith app ts (border v ts))
          else comp j (app f v) (app li0 vi0) (intersectionWith app ts (border v ts))
  _ -> VApp u v

fstVal, sndVal :: Val -> Val
fstVal (VPair a b)     = a
fstVal u               = VFst u
sndVal (VPair a b)     = b
sndVal u               = VSnd u

(@@) :: ToFormula a => Val -> a -> Val
(VTrans (VPLam i (VPathP p v0 v1)) psi u) @@ phi = case toFormula phi of
  Dir 0 -> v0 `face` (i~>1)
  Dir 1 -> v1 `face` (i~>1)
  f -> let uf = u @@ f
       in comp i (p @@ f) uf
               (unionSystem (border v0 (invSystem f Zero))
                            (unionSystem (border v1 (invSystem f One))
                                         (border uf (invSystem psi One))))
(VHComp i (VPathP p v0 v1) u us) @@ phi = case toFormula phi of
  Dir 0 -> v0 `face` (i~>1)
  Dir 1 -> v1 `face` (i~>1)
  f -> hcomp i (p @@ f) (u @@ f)
               (unionSystem (border v0 (invSystem f Zero))
                            (unionSystem (border v1 (invSystem f One))
                                         (mapSystem (@@ f) us)))
(VComp i (VPathP p v0 v1) u us) @@ phi = case toFormula phi of
  Dir 0 -> v0 `face` (i~>1)
  Dir 1 -> v1 `face` (i~>1)
  f -> comp i (p @@ f) (u @@ f)
              (unionSystem (border v0 (invSystem f Zero))
                           (unionSystem (border v1 (invSystem f One))
                                         (mapSystem (@@ f) us)))
(FastTer (PLam i u) rho) @@ phi = eval (sub (i,toFormula phi) rho) u
(VPLam i u) @@ phi         = act True u (i,toFormula phi)
v @@ phi = VAppFormula v (toFormula phi) -- error ("@@: this shouldn't happen " ++ show (showVal v) ++ " @@ " ++ show (toFormula phi))

-------------------------------------------------------------------------------
-- Composition and filling

hfill :: Name -> Val -> Val -> System Val -> Val
hfill i a u us = hcomp j a u (insertSystem (i ~> 0) u $ us `conj` (i,j))
  where j = fresh (Atom i,a,u,us)

hcomp :: Name -> Val -> Val -> System Val -> Val
hcomp i a u us | eps `member` us = (us ! eps) `face` (i ~> 1)
hcomp i a u us = case a of
  VPathP{} -> VHComp i a u us
  VSigma a f
    | isNonDep f -> VPair (hcomp i a (fstVal u) (mapSystem fstVal us))
                          (hcomp i (app f (VVar "impossible" VU)) (sndVal u) (mapSystem sndVal us))
    | otherwise -> 
      let (us1, us2) = (mapSystem fstVal us, mapSystem sndVal us)
          (u1, u2) = (fstVal u, sndVal u)
          u1fill = hfill i a u1 us1
          u1comp = hcomp i a u1 us1
      in VPair u1comp (comp i (app f u1fill) u2 us2)
  VU -> hcompUniv i u us
  VGlue b equivs ->
    let wts = mapWithKey (\al wal ->
                  app (equivFun wal)
                    (hfill i (equivDom wal) (u `face` al) (us `face` al)))
                equivs
        t1s = mapWithKey (\al wal ->
                hcomp i (equivDom wal) (u `face` al) (us `face` al)) equivs
        v = unglue u b equivs
        vs = mapWithKey (\al ual -> unglue ual (b `face` al) (equivs `face` al))
               us
        v1 = hcomp i b v (vs `unionSystem` wts)
    in glueElem v1 t1s
  VHCompU j b es ->
    let wts = mapWithKey (\al eal ->
                  eqFun (j,eal)
                    (hfill i (act True eal (j,Dir 1)) (u `face` al) (us `face` al)))
                es
        t1s = mapWithKey (\al eal ->
                hcomp i (act True eal (j,Dir 1)) (u `face` al) (us `face` al)) es
        v = unglueU u b (i,es)
        vs = mapWithKey (\al ual -> unglueU ual (b `face` al) (i,es `face` al)) us
        v1 = hcomp i b v (vs `unionSystem` wts)
    in glueElem v1 t1s
  FastTer (Sum _ n _) _
    | n `elem` ["Z","nat","bool"] -> u
    | otherwise -> error ("hcomp, unsupported datatype: " ++ n)
  FastTer (HSum _ _ _) _ -> VHComp i a u us
  VPi{} -> VHComp i a u us
  _ -> VHComp i a u us

-- For i:II |- a, phi # i, u : a (i/phi) we get fwd i a phi u : a(i/1)
-- such that fwd i a 1 u = u.   Note that i gets bound.
fwd :: Name -> Val -> Formula -> Val -> Val
fwd i a phi u = trans (VPLam i (act True a (i,phi `orFormula` Atom i))) phi u

comp :: Name -> Val -> Val -> System Val -> Val
comp i a u us | eps `member` us = (us ! eps) `face` (i ~> 1)
comp i a u us = case a of
    VPathP{} -> VComp i a u us
    VSigma a f
      | isNonDep f -> VPair (comp i a (fstVal u) (mapSystem fstVal us))
                            (comp i (app f (VVar "impossible" VU)) (sndVal u) (mapSystem sndVal us))
      | otherwise ->
        let (t1s, t2s) = (mapSystem fstVal us, mapSystem sndVal us)
            (u1,  u2)  = (fstVal u, sndVal u)
            fill_u1    = fill i a u1 t1s
            ui1        = comp i a u1 t1s
            comp_u2    = comp i (app f fill_u1) u2 t2s
        in VPair ui1 comp_u2
    VPi{} -> VComp i a u us
    -- VU -> compUniv u (mapSystem (VPLam i) us)
    -- VCompU a es -> compU i a es u us
    VGlue b equivs -> compGlue i b equivs u us    
    FastTer (Sum _ n _) _
      | n `elem` ["nat","Z","bool"] -> u
      | otherwise -> error ("comp, unsupported type: " ++ n)
    _ -> let j = fresh (Atom i,a,u,us)
         in hcomp j (a `face` (i ~> 1)) (trans (VPLam i a) (Dir Zero) u)
                    (mapWithKey (\al ual -> fwd i (a `face` al) (Atom j) (ual `swap` (i,j))) us)

compNeg :: Name -> Val -> Val -> System Val -> Val
compNeg i a u us = comp i (a `sym` i) u (us `sym` i)

fill :: Name -> Val -> Val -> System Val -> Val
fill i a u ts = comp j (a `conj` (i,j)) u (insertSystem (i ~> 0) u (ts `conj` (i,j)))
  where j = fresh (Atom i,a,u,ts)

-----------------------------------------------------------
-- Transport

trans :: Val -> Formula -> Val -> Val
trans _ (Dir One) u = u
trans (VPLam i a) phi u = case a of
  VPathP{} -> VTrans (VPLam i a) phi u
  VPi{} -> VTrans (VPLam i a) phi u
  VSigma{} -> transSigma (VPLam i a) phi u
  VU -> u
  VGlue b equivs -> transGlue i b equivs phi u
  VHCompU j b es -> transHCompU i b (j,es) phi u
  FastTer (Sum _ n _) _
    | n `elem` ["nat","Z","bool"] -> u
    | otherwise -> error ("trans, unsupported datatype: " ++ n)
  FastTer (HSum _ _ _) _ -> transHSum (VPLam i a) phi u
  _ -> VTrans (VPLam i a) phi u

transSigma :: Val -> Formula -> Val -> Val
transSigma (VPLam i a) phi u = case a of
  VSigma a f
    | isNonDep f -> VPair (trans (VPLam i a) phi (fstVal u))
                          (trans (VPLam i (app f (VVar "impossible" VU))) phi (sndVal u))
    | otherwise ->
      let (u1,u2) = (fstVal u, sndVal u)
          u1f     = transFill i a phi u1
      in VPair (trans (VPLam i a) phi u1) (trans (VPLam i (app f u1f)) phi u2)
  _ -> error "transSigma"

transHSum :: Val -> Formula -> Val -> Val
transHSum (VPLam i a@(FastTer (HSum _ n nass) env)) phi u
  | n `elem` ["S1","S2","S3","g2Trunc"] = u
  | otherwise = case u of
    VCon n us -> case lookupLabel n nass of
      Just tele -> VCon n (transps i tele env phi us)
      Nothing -> error $ "trans: missing constructor in hsum " ++ n
    VPCon n _ us psis -> case lookupPLabel n nass of 
      Just (tele,is,es) ->
        VPCon n (a `face` (i ~> 1)) (transps i tele env phi us) psis
      Nothing -> error $ "trans: missing path constructor in hsum " ++ n
    VHComp j _ v vs ->
      hcomp j (a `face` (i ~> 1)) (trans (VPLam i a) phi v)
              (mapWithKey (\al val ->
                 trans (VPLam i (a `face` al)) (phi `face` al) val) vs)
  
transFill :: Name -> Val -> Formula -> Val -> Val
transFill i a phi u = trans (VPLam j (a `conj` (i,j))) (phi `orFormula` NegAtom i) u
  where j = fresh (Atom i,a,phi,u)

transNeg :: Name -> Val -> Formula -> Val -> Val
transNeg i a phi u = trans (VPLam i (a `sym` i)) phi u

transFillNeg :: Name -> Val -> Formula -> Val -> Val
transFillNeg i a phi u = (transFill i (a `sym` i) phi u) `sym` i

transps :: Name -> [(Ident,Ter)] -> FastEnv -> Formula -> [Val] -> [Val]
transps i []         _ phi []     = []
transps i ((x,a):as) e phi (u:us) =
  let v   = transFill i (eval e a) phi u
      vi1 = trans (VPLam i (eval e a)) phi u
      vs  = transps i as (upd (x,v) e) phi us
  in vi1 : vs
transps _ _ _ _ _ = error "transps: different lengths of types and values"

-------------------------------------------------------------------------------
-- | HITs

pcon :: LIdent -> Val -> [Val] -> [Formula] -> Val
pcon c a@(FastTer (HSum _ _ lbls) rho) us phis = case lookupPLabel c lbls of
  Just (tele,is,ts) | eps `member` vs -> vs ! eps
                    | otherwise       -> VPCon c a us phis
    where rho' = subs (zip is phis) (updsTele tele us rho)
          vs   = evalSystem rho' ts
  Nothing           -> error "pcon"
pcon c a us phi     = VPCon c a us phi


-------------------------------------------------------------------------------
-- | Glue

-- An equivalence for a type a is a triple (t,f,p) where
-- t : U
-- f : t -> a
-- p : (x : a) -> isContr ((y:t) * Path a x (f y))
-- with isContr c = (z : c) * ((z' : C) -> Path c z z')

-- Extraction functions for getting a, f, s and t:
equivDom :: Val -> Val
equivDom = fstVal

equivFun :: Val -> Val
equivFun = fstVal . sndVal

equivContr :: Val -> Val
equivContr =  sndVal . sndVal

glue :: Val -> System Val -> Val
glue b ts | eps `member` ts = equivDom (ts ! eps)
          | otherwise       = VGlue b ts

glueElem :: Val -> System Val -> Val
glueElem v us | eps `member` us = us ! eps
glueElem v us = VGlueElem v us

unglue :: Val -> Val -> System Val -> Val
unglue w a equivs | eps `member` equivs = app (equivFun (equivs ! eps)) w
unglue (VGlueElem v us) _ _ = v
unglue w a equivs = VUnGlueElem w a equivs

extend :: Val -> Val -> System Val -> Val
extend b q ts = hcomp i b (fstVal q) ts'
  where i = fresh (b,q,ts)
        ts' = mapWithKey
                (\alpha tAlpha -> app ((sndVal q) `face` alpha) tAlpha @@ i) ts

mkFiberType :: Val -> Val -> Val -> Val
mkFiberType a x equiv = eval rho $
  Sigma $ Lam "y" tt (PathP (PLam (Name "_") ta) tx (App tf ty))
  where [ta,tx,ty,tf,tt] = map Var ["a","x","y","f","t"]
        rho = upds [("a",a),("x",x),("f",equivFun equiv),("t",equivDom equiv)] emptyEnv

transGlue :: Name -> Val -> System Val -> Formula -> Val -> Val
transGlue i a equivs psi u0 = glueElem v1' t1s'
  where
    v0 = unglue u0 (a `face` (i ~> 0)) (equivs `face` (i ~> 0))
    ai1 = a `face` (i ~> 1)
    alliequivs = allSystem i equivs
    psisys = invSystem psi One -- (psi = 1) : FF
    t1s = mapWithKey
            (\al wal -> trans (VPLam i (equivDom wal)) (psi `face` al) (u0 `face` al))
            alliequivs
    wts = mapWithKey (\al wal ->
              app (equivFun wal)
                (transFill i (equivDom wal) (psi `face` al) (u0 `face` al)))
            alliequivs
    v1 = comp i a v0 (border v0 psisys `unionSystem` wts)

    fibersys = mapWithKey
                 (\al x -> VPair x (constPath (v1 `face` al)))
                 (border u0 psisys `unionSystem` t1s)

    fibersys' = mapWithKey
                  (\al wal ->
                     extend (mkFiberType (ai1 `face` al) (v1 `face` al) wal)
                       (app (equivContr wal) (v1 `face` al))
                       (fibersys `face` al))
                  (equivs `face` (i ~> 1))

    t1s' = mapSystem fstVal fibersys'
    -- no need for a fresh name; take i
    v1' = hcomp i ai1 v1 (mapSystem (\om -> (sndVal om) @@ i) fibersys'
                           `unionSystem` border v1 psisys)

compGlue :: Name -> Val -> System Val -> Val -> System Val -> Val
compGlue i a equivs wi0 ws = glueElem vi1 usi1
  where ai1 = a `face` (i ~> 1)
        vs  = mapWithKey
                (\alpha wAlpha ->
                  unglue wAlpha (a `face` alpha) (equivs `face` alpha)) ws

        vsi1 = vs `face` (i ~> 1) -- same as: border vi1 vs
        vi0  = unglue wi0 (a `face` (i ~> 0)) (equivs `face` (i ~> 0)) -- in a(i0)

        vi1'  = comp i a vi0 vs           -- in a(i1)

        equivsI1 = equivs `face` (i ~> 1)
        equivs'  = filterWithKey (\alpha _ -> i `notMemberFace` alpha) equivs

        us'    = mapWithKey (\gamma equivG ->
                   fill i (equivDom equivG) (wi0 `face` gamma) (ws `face` gamma))
                 equivs'
        usi1'  = mapWithKey (\gamma equivG ->
                   comp i (equivDom equivG) (wi0 `face` gamma) (ws `face` gamma))
                 equivs'

        -- path in ai1 between vi1 and f(i1) usi1' on equivs'
        ls'    = mapWithKey (\gamma equivG ->
                   pathComp i (a `face` gamma) (vi0 `face` gamma)
                     (equivFun equivG `app` (us' ! gamma)) (vs `face` gamma))
                 equivs'

        fibersys = intersectionWith VPair usi1' ls' -- on equivs'

        wsi1 = ws `face` (i ~> 1)
        fibersys' = mapWithKey
          (\gamma equivG ->
            let fibsgamma = intersectionWith (\ x y -> VPair x (constPath y))
                              (wsi1 `face` gamma) (vsi1 `face` gamma)
            in extend (mkFiberType (ai1 `face` gamma) (vi1' `face` gamma) equivG)
                 (app (equivContr equivG) (vi1' `face` gamma))
                 (fibsgamma `unionSystem` (fibersys `face` gamma))) equivsI1

        vi1 = hcomp i ai1 vi1'
                (mapSystem sndVal fibersys' `unionSystem` mapSystem constPath vsi1)

        usi1 = mapSystem fstVal fibersys'

-- Assumes u' : A is a solution of us + (i0 -> u0)
-- The output is an L-path in A(i1) between comp i u0 us and u'(i1)
pathComp :: Name -> Val -> Val -> Val -> System Val -> Val
pathComp i a u0 u' us = VPLam j $ comp i a u0 us'
  where j   = fresh (Atom i,a,us,u0,u')
        us' = insertsSystem [(j ~> 1, u')] us

-------------------------------------------------------------------------------
-- | Composition in the Universe

-- any path between types define an equivalence
eqFun :: (Name,Val) -> Val -> Val
eqFun (i,e) = transNeg i e (Dir Zero)

unglueU :: Val -> Val -> (Name,System Val) -> Val
unglueU w b (i,es) | eps `member` es = eqFun (i,es ! eps) w
unglueU (VGlueElem v us) _ _ = v
unglueU w b (i,es) = VUnGlueElemU w b (i,es)

hcompUniv :: Name -> Val -> System Val -> Val
hcompUniv i b es | eps `member` es = act True (es ! eps) (i,Dir 1)
                 | otherwise       = VHCompU i b es

transHCompU :: Name -> Val -> (Name,System Val) -> Formula -> Val -> Val
transHCompU i a (j,es) psi u0 = glueElem v1' t1s'
  where
    (ai0,esi0) = (a,es) `face` (i ~> 0)
    (ai1,esi1) = (a,es) `face` (i ~> 1)

    v0 = unglueU u0 ai0 (j,esi0)

    allies = allSystem i es
    psisys = invSystem psi One -- (psi = 1) : FF

    -- Preprocess allies to avoid recomputing the faces in t1s and wts
    allies' = mapWithKey (\al eal ->
                (eal, act True eal (j,Dir 1), psi `face` al, u0 `face` al)) allies
    t1s = mapSystem
            (\(_,eal1,psial,u0al) -> trans (VPLam i eal1) psial u0al)
            allies'
    wts = mapSystem
            (\(eal,eal1,psial,u0al) -> eqFun (j,eal) (transFill i eal1 psial u0al))
            allies'

    v1 = comp i a v0 (border v0 psisys `unionSystem` wts)

    sys = border u0 psisys `unionSystem` t1s

    fibersys' = mapWithKey
                  (\al eal ->
                     lemEqConst i (j,eal) (v1 `face` al) (sys `face` al))
                  esi1

    t1s' = mapSystem fst fibersys'

    v1' = hcomp i ai1 v1 (mapSystem snd fibersys' `unionSystem` border v1 psisys)

-- Extend a partial element (aalpha, <_> f aalpha) in the fiber over b
-- to a total one where f is transNeg of eq.  Applies the second
-- component to the fresh name i.
lemEqConst :: Name -> (Name,Val) -> Val -> System Val -> (Val,Val)
lemEqConst i (j,eq@(VPLam _ (FastTer (Sum _ n _) _))) b as
  | n `elem` ["Z","nat","bool"] = (hcomp j eq b as,hfill i eq b as)
lemEqConst i (j,eq@(VPLam _ (FastTer (HSum _ n _) _))) b as
  | n `elem` ["S1","S2","S3","g2Trunc"] = (hcomp j eq b as,hfill i eq b as)
lemEqConst i (j,eq) b as = (a,p)
 where
   adwns = mapWithKey (\al aal ->
               let eqaj = eq `face` al
               in transFillNeg j eqaj (Dir Zero) aal) as
   left = fill j eq b adwns
   a = comp j eq b adwns
   -- a = left `face` (j ~> 1)

   right = transFillNeg j eq (Dir Zero) a

   p = compNeg j eq a (insertsSystem [ (i ~> 0, left), (i ~> 1, right)] adwns)
