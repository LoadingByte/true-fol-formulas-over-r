-- Decision algorithm for real numbers, list of true sentences
-- Authors: Philip Lukert, Felix Mujkanovic
-- Date: 05 September 2018

import Data.List
import Data.Maybe



data Term = Zero | One | Var Integer | Neg Term | Inv Term | Add Term Term | Mul Term Term deriving (Eq)
data Proposition = Equals Term Term | Less Term Term deriving (Eq)
data Formula = Prop Proposition | Not Formula | Imp Formula Formula | Forall Integer Formula deriving (Eq)


instance Show Term where
  show Zero = "0"
  show One = "1"
  show (Var 0) = "x"
  show (Var 1) = "y"
  show (Var 2) = "z"
  show (Var n) = "x" ++ show n
  show (Neg t) = "-" ++ show t
  show (Inv t) = show t ++ "⁻¹"
  show (Add t (Neg u)) = "⟨" ++ show t ++ "-" ++ show u ++ "⟩"
  show (Add t u) = "⟨" ++ show t ++ "+" ++ show u ++ "⟩"
  show (Mul t (Inv u)) = "⟨" ++ show t ++ "÷" ++ show u ++ "⟩"
  show (Mul t u) = "⟨" ++ show t ++ "⋅" ++ show u ++ "⟩"

instance Show Proposition where
  show (Equals p q) = show p ++ "=" ++ show q
  show (Less   p q) = show p ++ "<" ++ show q

instance Show Formula where
  show (Prop p) = show p
  show (Not f) = "¬" ++ show f
  show (Imp f g) = "(" ++ show f ++ " → " ++ show g ++ ")"
  show (Forall n f) = "∀" ++ show (Var n) ++ ". " ++ show f ++ ""



-- What follows is a definition of all the basic "static" axioms of ℝ.

orr x y = Imp (Not x) y
andd x y = Not $ Imp x (Not y)

axiomsAdd = [
  Forall 0 $ Prop $ Equals (Add (Var 0) Zero) (Var 0),
  Forall 0 $ Forall 1 $ Prop $ Equals (Add (Var 0) (Var 1))(Add (Var 1) (Var 0)),
  Forall 0 $ Forall 1 $ Forall 2 $ Prop $ Equals (Add (Var 0) (Add (Var 1)(Var 2))) (Add (Add (Var 0) (Var 1)) (Var 2)),
  Forall 0 $ Not $ Forall 1 $ Not $ Prop $ Equals (Add (Var 0) (Var 1)) Zero
  ]

axiomsMul = [
  Forall 0 $ Prop $ Equals (Mul (Var 0) One) (Var 0),
  Forall 0 $ Forall 1 $ Prop $ Equals (Mul (Var 0) (Var 1))(Mul (Var 1) (Var 0)),
  Forall 0 $ Forall 1 $ Forall 2 $ Prop $ Equals (Mul (Var 0) (Mul (Var 1)(Var 2))) (Mul (Mul (Var 0) (Var 1)) (Var 2)),
  Forall 0 $ Imp (Not (Prop (Equals (Var 0) Zero))) $ Not $ Forall 1 $ Not $ Prop $ Equals (Mul (Var 0) (Var 1)) One
  ]

axiomsSpecial = [Not $ Prop $ Equals One Zero,
  Forall 0 $ Forall 1 $ Forall 2 $ Prop $ Equals (Mul (Var 0) (Add (Var 1)(Var 2))) (Add (Mul (Var 0)(Var 1))(Mul (Var 0)(Var 2)))
  ]

axiomsRel = [
  Forall 0 $ orr (Prop (Less (Var 0) Zero)) $ orr (Prop (Equals (Var 0) Zero)) $ Prop (Less Zero (Var 0)),
  Forall 0 $ Forall 1 $ Forall 2 $ Imp (andd (Prop (Less (Var 0) (Var 1))) (Prop (Less (Var 1) (Var 2)))) (Prop (Less (Var 0) (Var 2))),
  Forall 0 $ Not $ Prop $ Less (Var 0) (Var 0),
  Forall 0 $ Forall 1 $ Forall 2 $ Imp (Prop (Less (Var 0)(Var 1))) (Prop(Less (Add (Var 0)(Var 2))(Add (Var 1)(Var 2)))),
  Forall 0 $ Forall 1 $ Forall 2 $ Imp (andd (Prop(Less (Var 0)(Var 1)))(Prop(Less Zero (Var 2)))) (Prop(Less(Mul (Var 0)(Var 2))(Mul(Var 1)(Var 2))))
  ]

staticAxioms =
  axiomsAdd ++
  axiomsMul ++
  axiomsSpecial ++
  axiomsRel



replaceT n (Zero) t = Zero
replaceT n (One) t = One
replaceT n (Var v) t = if v == n then t else Var v
replaceT n (Add p q) t = Add (replaceT n p t) (replaceT n q t)
replaceT n (Mul p q) t = Mul (replaceT n p t) (replaceT n q t)
replaceP n (Equals p q) t = Equals (replaceT n p t) (replaceT n q t)
replaceP n (Less p q) t = Less (replaceT n p t) (replaceT n q t)
replaceF n (Prop p) t = Prop (replaceP n p t)
replaceF n (Not f) t = Not (replaceF n f t)
replaceF n (Imp f g) t = Imp (replaceF n f t) (replaceF n g t)
replaceF n (Forall x f) t = Forall n (replaceF x f t)

canInsert :: Integer -> Formula -> Term -> Bool
canInsert n (Prop p) t = True
canInsert n (Not f) t = canInsert n f t
canInsert n (Imp f g) t = (canInsert n f t) && (canInsert n g t)
canInsert n (Forall x f) t = canInsert n f t && ((not (n `elem` (varsInFormula f))) || (not (x `elem` (varsInTerm t))))



-- An infinite list of all terms, grouped in sublists of increasing length.
terms :: [[Term]]
terms = growLengthwise [negGrower, invGrower] [addGrower, mulGrower] ([Zero, One, Var 0] : map (\x -> [Var x]) [1..])
  where
    negGrower :: Term -> [Term]
    negGrower t = [Neg t]

    invGrower :: Term -> [Term]
    invGrower t = [Inv t]

    addGrower :: Term -> Term -> [Term]
    addGrower t u = [Add t u]

    mulGrower :: Term -> Term -> [Term]
    mulGrower t u = [Mul t u]


-- An infinite list of all propositions, grouped in sublists of increasing length.
-- This list contains both true and false propositions.
propositions :: [[Proposition]]
propositions = combineLengthwise [equalsCombinator, lessCombinator] [] terms
  where
    equalsCombinator :: Term -> Term -> [Proposition]
    equalsCombinator t u = [Equals t u]

    lessCombinator :: Term -> Term -> [Proposition]
    lessCombinator t u = [Less t u]


-- An infinite list of all first order logic formulas, grouped in sublists of increasing length.
-- This list contains both true and false formulas.
formulas :: [[Formula]]
formulas = map (filter formulaValid) $ growLengthwise [notGrower, forallGrower] [impGrower] (map (map (\p -> Prop p)) propositions)
  where
    notGrower :: Formula -> [Formula]
    notGrower f = [Not f]

    forallGrower :: Formula -> [Formula]
    forallGrower f = [Forall x f | x <- freeVarsInFormula f]

    impGrower :: Formula -> Formula -> [Formula]
    impGrower f g = [Imp f g]

    formulaValid :: Formula -> Bool
    formulaValid f = freeVarsInFormula f == []


-- An infinite list of all TRUE first order logic formulas you can obtain by putting
-- all possible formulas into the basic axioms of first order logic.
-- Note that the resulting list of formulas is no longer strictly ordered by length since
-- the axioms do more advanced stuff than adding just one operator.
-- However, the list is still kind of ordered.
laxiomInsts :: [Formula]
laxiomInsts = concat $ combineLengthwise [laxiom1, laxiom3, laxiom4, laxiom5] [laxiom2] formulas
  where
    laxiom1 :: Formula -> Formula -> [Formula]
    laxiom1 a b = [Imp a (Imp b a)]

    laxiom2 :: Formula -> Formula -> Formula -> [Formula]
    laxiom2 a b c = [Imp (Imp a (Imp b c)) (Imp (Imp a b) (Imp a c))]

    laxiom3 :: Formula -> Formula -> [Formula]
    laxiom3 a b = [Imp (Imp (Not b) (Not a)) (Imp a b)]

    laxiom4 :: Formula -> Formula -> [Formula]
    laxiom4 a (Prop (Equals t1 t2)) = [replaceF x a t1 | x <- freeVarsInFormula a] ++ [replaceF x a t2 | x <- freeVarsInFormula a]
    laxiom4 a (Prop (Less   t1 t2)) = [replaceF x a t1 | x <- freeVarsInFormula a] ++ [replaceF x a t2 | x <- freeVarsInFormula a]
    laxiom4 _ _                     = []

    laxiom5 :: Formula -> Formula -> [Formula]
    laxiom5 a b = [Imp (Forall x (Imp a b)) $ Imp a $ Forall x b | x <- freeVarsInFormula b, x `notElem` freeVarsInFormula a]



varsInTerm :: Term -> [Integer]
varsInTerm (Var n)   = [n]
varsInTerm (Add t u) = (varsInTerm t) ++ (varsInTerm u)
varsInTerm (Mul t u) = (varsInTerm t) ++ (varsInTerm u)
varsInTerm _ = []

varsInProp :: Proposition -> [Integer]
varsInProp (Equals p q) = (varsInTerm p) ++ (varsInTerm q)
varsInProp (Less   p q) = (varsInTerm p) ++ (varsInTerm q)

varsInFormula :: Formula -> [Integer]
varsInFormula (Prop p)       = varsInProp p
varsInFormula (Not f)        = varsInFormula f
varsInFormula (Imp f g)      = (varsInFormula f) ++ (varsInFormula g)
varsInFormula (Forall var f) = varsInFormula f

freeVarsInFormula :: Formula -> [Integer]
freeVarsInFormula (Prop p)       = varsInProp p
freeVarsInFormula (Not f)        = freeVarsInFormula f
freeVarsInFormula (Imp f g)      = (freeVarsInFormula f) ++ (freeVarsInFormula g)
freeVarsInFormula (Forall var f) = deleteAll var (freeVarsInFormula f)



-- The final infinite list of all TRUE formulas.
-- It is generated by taking the axioms of ℝ, slowly adding laxiomInsts and repeatedly
-- applying modus ponens and generalization over time.
trueFormulas :: [Formula]
trueFormulas = staticAxioms ++ (iter staticAxioms laxiomInsts)
  where
    iter :: [Formula] -> [Formula] -> [Formula]
    iter prevTrueFormulas (a:axioms) = let newTrueFormulas = (step prevTrueFormulas a)
                                       in  newTrueFormulas ++ (iter (prevTrueFormulas ++ newTrueFormulas) axioms)

    step :: [Formula] -> Formula -> [Formula]
    step old newAxiom = [newAxiom] ++ (nub $ applyMponens old [newAxiom]) ++ (applyGeneralization newAxiom)


applyMponens :: [Formula] -> [Formula] -> [Formula]
applyMponens [] _  = []
applyMponens _  [] = []
applyMponens fs gs = concat [(applyMponensSingle f g) ++
                             (applyMponensSingle g f) | f <- fs, g <- gs]
  where
    applyMponensSingle :: Formula -> Formula -> [Formula]
    applyMponensSingle f (Imp p c) = if   f == p
                                     then [c]
                                     else []
    applyMponensSingle _ _         = []


applyGeneralization :: Formula -> [Formula]
applyGeneralization f = foldl (\list x -> ((Forall x f):list)) [] (freeVarsInFormula f)



---------------
-- Utilities --
---------------


deleteAll :: (Eq a) => a -> [a] -> [a]
deleteAll e = filter (/=e)


nthl :: [[a]] -> Int -> [a]
nthl [] _     = []
nthl (x:_)  1 = x
nthl (_:xs) n = nthl xs (n-1)


combineLengthwise :: [a -> a -> [b]] -> [a -> a -> a -> [b]] -> [[a]] -> [[b]]
combineLengthwise bCombinators tCombinators sourceLenGroups = doCL 1
  where
    -- doCL :: Int -> [[b]]
    doCL currLen = currLenGroup : doCL (currLen+1)
      where
        -- currLenGroup :: [b]
        currLenGroup =
          concat [bCombinator a1 a2 | bCombinator <- bCombinators,
                                             grp1 <- [1..(currLen-2)], let grp2 = currLen - grp1 - 1,
                                               a1 <- sourceLenGroups `nthl` grp1,
                                               a2 <- sourceLenGroups `nthl` grp2] ++
          concat [tCombinator a1 a2 a3 | tCombinator <- tCombinators,
                                                grp1 <- [1..(currLen-4)],
                                                grp2 <- [1..(currLen-grp1-3)], let grp3 = currLen - grp1 - grp2 - 2,
                                                  a1 <- sourceLenGroups `nthl` grp1,
                                                  a2 <- sourceLenGroups `nthl` grp2,
                                                  a3 <- sourceLenGroups `nthl` grp3]


growLengthwise :: [a -> [a]] -> [a -> a -> [a]] -> [[a]] -> [[a]]
growLengthwise uGrowers bGrowers initLenGroups = doGL initLenGroups []
  where
    -- doGL :: [[a]] -> [[a]] -> [[a]]
    doGL (currInitLenGroup:nextInitLenGroups) prevLenGroups = currLenGroup : (doGL nextInitLenGroups (prevLenGroups ++ [currLenGroup]))
      where
        currLen :: Int
        currLen = length prevLenGroups + 1

        -- currLenGroup :: [a]
        currLenGroup =
          currInitLenGroup ++
          concat [uGrower a | uGrower <- uGrowers,
                                    a <- (prevLenGroups `nthl` (currLen-1))] ++
          concat [bGrower a1 a2 | bGrower <- bGrowers,
                                     grp1 <- [1..(currLen-2)], let grp2 = currLen - grp1 - 1,
                                       a1 <- prevLenGroups `nthl` grp1,
                                       a2 <- prevLenGroups `nthl` grp2]



printListWithNewlines :: (Show a) => [a] -> IO ()
printListWithNewlines xs = putStr $ (concat . intersperse "\n" . map (\(n,s) -> show n ++ "\t" ++ show s) . zip [1..] $ xs) ++ "\n"

printTerms = printListWithNewlines $ concat terms
printPropositions = printListWithNewlines $ concat propositions
printFormulas = printListWithNewlines $ concat formulas
printLaxiomInsts = printListWithNewlines laxiomInsts
printStaticAxioms = printListWithNewlines staticAxioms
printTrueFormulas = printListWithNewlines trueFormulas

main = printTrueFormulas
