--------------------------------------------------------------------------------
-- 1. You are required to use the following type for propositional formulae, where conjunctions and disjunctions work on list of formulae.
-- 2. Derive or instantiate only the essential type classes. (finished)

data Formula
  = Const Bool
  | Prop String
  | Not Formula
  | Or [Formula]
  | And [Formula]
  | Impl Formula Formula
  | Equiv Formula Formula
  deriving (Eq)           -- only Eq class is needed to be derived, since we are going to define our own way to display formulae and ... why is Eq needed

--------------------------------------------------------------------------------
-- 3. Instantiate the Show type class so that the false constant is represented. (finished)
-- by "F", the true constant is represented by "T", ¬ is represented by "~",
-- ∧ is represented by "&", ∨ is represented by "|", → is represented by "->",
-- and ↔ is represented by "<->".

-- False => "F"
-- True  => "T"
-- Not   => "~"
-- And   => "&"
-- Or    => "|"
-- Impl  => "->"
-- Equiv => "<->"

-- Equiv (Prop "q") (Or [Const False, Not (Prop "r")])
-- should print: (q <-> (F | ~r))

instance Show Formula where
  show (Const False) = "F"                                            -- Const False => F
  show (Const True)  = "T"                                            -- Const True  => T
  show (Prop a)      = a                                              -- e.g. Prop "q" => q
  show (Not a)       = "~" ++ show a                                  -- e.g. Not (Prop "q") => ~q
  
  show (Or [])       = ""                                             -- since Or and And are allowed to have more than 2 elements inside, 
  show (Or [a])      = show a                                         -- we put brackets and the pipe recursively
  show (Or (x:xs))   = "(" ++ show x ++ " | " ++ show (Or xs) ++ ")"  -- also need to deal with base cases where the list is empty, or has 1 element
                                                                      -- to prevent errors, and wrong prints.
  
  show (And [])      = ""                                             -- exactly the same for And, just '|' replaced with '&'
  show (And [f])     = show f
  show (And (x:xs))  = "(" ++ show x ++ " & " ++ show (And xs) ++ ")"
  
  show (Impl a b)    = "(" ++ show a ++ " -> " ++ show b ++ ")"       -- implication and equivalence have exactly 2 arguments.
  show (Equiv a b)   = "(" ++ show a ++ " <-> " ++ show b ++ ")"      -- so print directly, no need for recursion.


-- show (And (x:xs))  = "(" ++ show x ++ " & " ++ show (And xs) ++ ")"
-- show (Or (x:xs))   = "(" ++ show x ++ " | " ++ show (Or xs) ++ ")"

-- this is the part of the old version of the instantiation, I realised that this part of the code made simplify function
-- act faulty for dealing cases like ((p | q) | r) => (p | q | r), since it adds parentheses every split.

-- but I did not figure out how to deal with this problem :'(

--------------------------------------------------------------------------------
-- 4. Implement a function 'toNNF' performing
-- the negation normal form transformation, and having type:

-- toNNF :: Formula -> Formula

toNNF :: Formula -> Formula
toNNF (Const a)   = Const a                                     -- const and prop are the atoms
toNNF (Prop a)    = Prop a                                      -- just return them
toNNF (Not c)     = case c of
  Const a        -> Const (not a)                               -- negates the boolean value using the 'not' keyword
  Prop a         -> Not (Prop a)                                -- adds not in front of a proposition (mindblowing!!)
  Not a          -> toNNF a                                     -- double negations mean no negation
  Or xs          -> toNNF (And (map Not xs))                    -- map :: (a -> b) -> [a] -> [b]
  And xs         -> toNNF (Or (map Not xs))                     -- ~(p | q) => (~p & -q), ~(p & q) => (~p | ~q)
  Impl a b       -> toNNF (And [a, Not b])                      -- ~(p -> q) => (p & ~q)
  Equiv a b      -> toNNF (Or [And [a, Not b], And [Not a, b]]) -- ~(p <-> q) => ((p & ~q) | (~p & q))
toNNF (Or xs)     = Or (map toNNF xs)                           -- call recursively till it finds the atoms (const or prop) 
toNNF (And xs)    = And (map toNNF xs)                          -- the same for and
toNNF (Impl a b)  = toNNF (Or [Not a, b])                       -- (p -> q) => (~p | q)
toNNF (Equiv a b) = toNNF (And [Impl a b, Impl b a])            -- (p <-> q) => (p -> q) & (q -> p)

--------------------------------------------------------------------------------
-- 5. Implement a function 'simplify' that performs the given simplifications 
-- on a formula in negation normal form, and having type:

-- simplify :: Formula -> Formula                             

-- (p | ~p) => T
-- (p & ~p) => F
-- (p | p) => p
-- (p & p) => p
-- (p & T) => p
-- (p | F) => p
-- (p & F) => F
-- (p | T) => T
-- (p | (q | r)) => p | q | r (failed to fix)
-- (p & (q & r)) => p & q & r (failed to fix)

simplify :: Formula -> Formula
simplify (Const b)   = Const b                     -- same thing here as toNNF
simplify (Prop p)    = Prop p                      -- (fabio is a great lecturer <3)

                                                   -- ghci> simplify (Not (Or [Const False, Prop "p"]))
                                                   -- ~(F | p)
                                                   -- ghci> :r
                                                   -- [1 of 2] Compiling Main             ( 39228649.hs, interpreted ) [Source file changed]
                                                   -- Ok, one module loaded.
                                                   -- ghci> simplify (Not (Or [Const False, Prop "p"]))
                                                   -- ~p

simplify (Not c)  = case simplify c of             -- had to put simplify c of instead of c, to make sure c is in the simplest form.
  Const a        -> Const (not a)                  -- otherwise it might not catch some cases, like the example above.
  Prop a         -> Not (Prop a)                   -- we do not deal with Impl and Equiv here, since toNNF already removed them.
  others         -> Not others
simplify (Or xs)  = simplifyOr (map simplify xs)   -- call simplifyOr
simplify (And xs) = simplifyAnd (map simplify xs)  -- call simplifyAnd

simplifyOr :: [Formula] -> Formula
simplifyOr formulae = case formulae of
  _ | Const True `elem` formulae -> Const True                                      -- if True is found inside, the result is True: (p | T) => T
  _ -> let falseRemoved = filter (/= Const False) formulae in case falseRemoved of  -- remove all Falses from the formulae
    [] -> Const False                                                               -- return False if empty list (all elements were False)
    _  -> if hasComplement falseRemoved                                             -- if (p | ~p) pair is found
      then Const True                                                               -- return True: (p | ~p) => T
      else case removeDuplicates falseRemoved of                                    -- remove duplicates from falseRemoved
        [x] -> x                                                                    -- (p | p) => p
        xs  -> Or xs                                                                -- other cases like (p | q), (p | q | r), ...
    where
      hasComplement xs = any (\y -> any (isComplementPair y) xs) xs                 -- temporary function to check if there is a complement (returns Bool)

simplifyAnd :: [Formula] -> Formula
simplifyAnd formulae = case formulae of
  _ | Const False `elem` formulae -> Const False                                    -- If False is found inside, the result is False: (p & F) => F
  _ -> let trueRemoved = filter (/= Const True) formulae in case trueRemoved of     -- Define a list with all Trues removed 
    [] -> Const True                                                                -- Return True if empty list (all elements were True)
    _  -> if hasComplement trueRemoved                                              -- if (p & ~p) pair is found
      then Const False                                                              -- return False: (p & ~p) => F
      else case removeDuplicates trueRemoved of                                     -- remove duplicates from trueRemoved
        [x] -> x                                                                    -- (p & p) => p
        xs  -> And xs                                                               -- other cases like (p & q), (p & q & r), ...
    where
      hasComplement xs = any (\y -> any (isComplementPair y) xs) xs


-- A helper function to remove duplicates.
-- Referenced Mahmoud's answer from Stack Overflow: 
-- https://stackoverflow.com/questions/16108714/removing-duplicates-from-a-list-in-haskell-without-elem
removeDuplicates :: Eq a => [a] -> [a]
removeDuplicates []     = []
removeDuplicates (x:xs) = x : removeDuplicates (filter (/= x) xs)

-- A helper to check if the two elements are negations of each other.
isComplementPair :: Formula -> Formula -> Bool
isComplementPair (Prop x) (Not (Prop y)) = x == y   -- check p ~p 
isComplementPair (Not (Prop x)) (Prop y) = x == y   -- need to also check ~p p 
isComplementPair _ _                     = False    -- False otherwise

--------------------------------------------------------------------------------
-- 6. Implement appropriate types for tableaux branches and for tableaux.

type Branch = [Formula]   -- Branches are lists of formulae
type Tableau = [Branch]   -- Tableaux are lists of branches
                          -- did not have to implement a binary tree type to traverse
                          -- it is actually way easier to compare elements to detect contradiction this way

--------------------------------------------------------------------------------
-- 7. Implement functions performing rule applications
-- (i.e., at least one function per rule).

-- Finds or-rule and returns it with the remaining branch.
orRule :: Branch -> Maybe (Formula, Branch)
orRule []     = Nothing                 -- returns Nothing when the branch is empty
orRule (x:xs) = case x of
  Or _ -> Just (x, xs)                  -- if the head of the branch starts with an Or, returns it with the remaining branch 
  _    -> case orRule xs of             -- check the rest
    Just (a, rest) -> Just (a, x:rest)  -- add x back so that you do not modify the size of the branch
    Nothing        -> Nothing           -- nothing found

-- Find the first AND formula in the branch (if any)
andRule :: Branch -> Maybe (Formula, Branch)
andRule []     = Nothing                -- returns Nothing when the branch is empty
andRule (x:xs) = case x of
  And _ -> Just (x, xs)                 -- if the head of the branch starts with an And, return it with the remaining branch
  _     -> case andRule xs of           -- check the rest
    Just (a, rest) -> Just (a, x:rest)  -- add x back so that you do not modify the size of the branch
    Nothing        -> Nothing           -- nothing found

-- Checks if there is a contradiction.
notRule :: Branch -> Bool
notRule branch =
  -- the condition is if the branch has F or a pair of formulae that are negations of each other
  Const False `elem` branch || any (\x -> any (isComplementPair x) branch) branch

--------------------------------------------------------------------------------
-- 8. Implement a function 'expand' that expand a tableau in such a way that
-- the and-rule is always applied before the or-rule.

expand :: Branch -> Maybe [Branch]
expand a =
  let branch = filter (/= Const True) a in                            -- remove Trues from the branch
    if notRule branch                                                 -- and apply it to the notRule
      then Nothing                                                    -- true means expansion is impossible
      else case andRule branch of                                     -- and-rule (before or-rule)
        Just (And x, xs) -> expand (xs ++ x)                          -- decompose when And is found, recursively expand the branch
        Nothing -> case orRule branch of                              -- or-rule
          Just (Or x, rest) ->
            let branchRes = map (\y -> expand (rest ++ [y])) x        -- do expansion
                openBranches = concat [xs | Just xs <- branchRes] in  -- save all open branches from branchRes
              if null openBranches                                    -- no open branch is found, so closed
                then Nothing
                else Just openBranches
          Nothing -> Just [branch]                                    -- no more and, or to expand

--------------------------------------------------------------------------------
-- 9. Implement a function 'checkSAT' with the following type:

-- checkSAT :: Formula -> String

-- where given a formula, it returns
-- "UNSAT" if the formula is unsatisfiable; or
-- "SAT with [...]" where the list contains all propositions or their negations
-- occurring on the branch, and without any repetition

checkSAT :: Formula -> String
checkSAT a
  | mBranches == Nothing = "UNSAT"                                      -- if the expansion return Nothin, the formula is unsatisfiable
  | otherwise     = "SAT with " ++ show (collectAtoms (head branches))  -- otherwise take the head from the open branch, extract the atoms and display
  where
    aInNNF      = toNNF a               -- make the formulae in NNF form
    aSimplified = simplify aInNNF       -- simplify it
    mBranches   = expand [aSimplified]  -- expand the tableau
    branches    = case mBranches of     -- extract the branches
      Just xs -> xs
      Nothing -> []
      
-- A helper to extract the formula literal from a branch.
collectAtoms :: Branch -> [Formula]
collectAtoms = removeDuplicates . filter isAtomic
  where
    isAtomic (Prop _)       = True   -- p
    isAtomic (Not (Prop _)) = True   -- ~p
    isAtomic (Const _)      = True   -- T, F
    isAtomic _              = False  -- no other cases, return False


-- ⠀⠀⠀⠀ ⠀⠀⠀⣀⠤⠔⠒⠒⡄⢀⣠⠤⠤⠦⡄⠀
-- ⠀⠀⠀⠀⠀⢀⡴⠋⠀⠀⠀⣀⠴⠊⣡⣴⣾⡿⣣⠃⠀⠀
-- ⠀⠀⠀⠀⢰⠋⠀⠀⠀⡤⠊⠁⣠⣾⡿⠟⣉⠴⠁⠀
-- ⠀⠀⠀⡠⠓⠀⠀⠀⠘⠁⢒⣿⠍⠓⠒⠉⠀⠀⠀⠀⠀⠀
-- ⠀⢠⠞⠀⠀⠀⠀⠀⠀⠀⠀⠀⠑⣄⠀⠀⠀⠀⠀⠀⠀⠀
-- ⠀⡏⠀⠀⠀⠀⠴⠂⠀⠀⠀⠀⠀⠘⢦⠀⠀⠀⠀⠀⠀⠀
-- ⢸⠘⠉⠀⠀⠀⣴⣶⢶⢀⠤⠀⠀⠀⠀⡇⠀⠀⠀⠀⠀⠀
-- ⠀⢷⣿⣵⣴⡆⢙⠉⡘⠟⠉⠁⠀⢀⡼⠁⠀⠀⠀⠀⠀⠀
-- ⢀⣾⡉⠣⠵⠶⠎⠉⠀⠀⠀⡠⠖⠛⠉⠉⠉⠙⢦⡀⠀⠀
-- ⠀⠊⠑⠂⠀⠤⣄⠀⠀⠀⠀⠀⠀⢀⣠⠄⠒⠀⠘⠁⠀⠀
-- ⣴⣒⠤⢤⡠⠔⡏⠀⠀⣀⠀⠀⠀⠀⠈⠙⠒⠢⢴⠑⢢⠀
-- ⠷⡀⠁⠀⠀⠈⡏⠑⠊⠉⠀⠀⠀⠀⠀⠀⠀⠀⠈⡇⢠⠁
-- ⠀⠈⠉⠉⠉⠉⠱⡀⠀⠀⠀⠀⠰⠀⠀⠀⠀⠀⠀⡏⠁⠀
-- ⠀⠀⠀⠀⠀⠀⢸⠉⠒⠤⠤⢤⡇⠀⠀⠀⠀⢀⢼⣇⠀⠀
-- ⠀⠀⠀⠀⠀⢠⠶⠿⠤⠤⠔⠛⡞⠦⣄⡠⡤⢊⣾⠟⠀⠀
-- ⠀⠀⠀⠀⠀⢱⣤⣤⣤⠠⢶⡿⠀⠀⠀⠙⠶⠽⠟⠀⠀⠀
-- ⠀⠀⠀⠀⠀⠀⠀⠉⠁⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀