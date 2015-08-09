data Term = Var String | Const String deriving (Show, Eq)
data Predicate = Pr (String,[Term]) deriving Show
data Goals = G [Predicate] deriving Show
data Rule = R (Predicate,Goals) deriving Show
data Solution =  Yes [(Term,Term)] | No deriving (Show, Eq)
data KnowledgeBase = KB [Rule] deriving Show

unifyWithHead (Pr (name1,x)) (Pr (name2,y)) | (name1 /= name2) || (length x  /= length y) = No
											| correct list = Yes (filterFromContsants list)
											| otherwise = No where list = match x y

match [] [] = []
match ((Var x):xs) ((Const y):ys) = (Var x,Const y):match xs ys
match ((Var x):xs) ((Var y):ys) = (Var y,Var x):match xs ys
match ((Const x):xs) ((Var y):ys) = (Var y,Const x):match xs ys
match ((Const x):xs) ((Const y):ys) = (Const x,Const y):match xs ys

correct [] = True
correct ((Var x,Var y):xs) = correct xs
correct ((Var x,Const y):xs) = correct xs
correct ((Const x,Const y):xs) | x == y = correct xs
							   | otherwise = False

filterFromContsants [] = []
filterFromContsants ((Const x,Const y):xs) = filterFromContsants xs
filterFromContsants ((Var x,Var y):xs) = ((Var x,Var y):(filterFromContsants xs))
filterFromContsants ((Var x,Const y):xs) = ((Var x,Const y):(filterFromContsants xs))

applySolSubInBody _ (G []) = G []
applySolSubInBody (Yes sol) (G ((Pr (name,b)):bs)) = G (returnSubs sol ((Pr (name,b)):bs))

returnSubs sol [] = []
returnSubs sol ((Pr (name,b)):bs) = ((Pr (name,(subGoal sol b))):(returnSubs sol bs))

subGoal sol [] = []
subGoal sol (t:ts) = (x:(subGoal sol ts)) where x = returnValue sol t 

returnValue [] x = x
returnValue (s:sols) (Const x) = returnValue sols (Const x)
returnValue (((Var sol,Const sub)):sols) (Var x) | x == sol = Const sub
												 | otherwise = returnValue sols (Var x)
returnValue (((Var sol,Var sub)):sols) (Var x) | x == sol = Var sub
											   | otherwise = returnValue sols (Var x)

allSolutions (Pr q) (KB kb) = allSolutions2 (Pr q) kb kb

allSolutions2 _ [] _ = []
allSolutions2 (Pr q) ((R ((Pr r),(G body))):rs) kb | ans == No = allSolutions2 (Pr q) rs kb
												   | length body == 0 = (ans:(allSolutions2 (Pr q) rs kb))
												   | areAllTermsVars q = ((applyOnBody (applySolSubInBody ans (G body)) kb)++(allSolutions2 (Pr q) rs kb))
												   | otherwise = filterFromYeses (filterSolutions (ans:((applyOnBody (applySolSubInBody ans (G body)) kb)++(allSolutions2 (Pr q) rs kb)))) where ans = unifyWithHead (Pr q) (Pr r)

areAllTermsVars (n,v) = areAllTermsVars2 v
areAllTermsVars2 [] = True
areAllTermsVars2 ((Var v):vs) = True && areAllTermsVars2 vs
areAllTermsVars2 ((Const v):vs) = False

applyOnBody (G []) _ = []
applyOnBody (G (g:gs)) kb = evaluateSolution allSolsOfg (G gs) kb where allSolsOfg = allSolutions g (KB kb)

evaluateSolution [] _ _ = []
evaluateSolution x (G []) _ = x
evaluateSolution (s:ss) (G g) kb = (addSolution s x)++(evaluateSolution ss (G g) kb) where x = applyOnBody (applySolSubInBody s (G g)) kb

addSolution (Yes l) [] = []
addSolution (Yes l) ((Yes l2):ss) = ((Yes (l++l2)):(addSolution (Yes l) ss))

filterSolutions [] = []
filterSolutions ((Yes s):ss) = ((Yes (filterSolutionFromNonWantedTerms s)):(filterSolutions ss))

filterSolutionFromNonWantedTerms [] = []
filterSolutionFromNonWantedTerms ((Var x, Var y):ts) = filterSolutionFromNonWantedTerms ts
filterSolutionFromNonWantedTerms ((Var x, Const y):ts) | x <= "L" = ((Var x, Const y):(filterSolutionFromNonWantedTerms ts))
													   | otherwise = filterSolutionFromNonWantedTerms ts

filterFromYeses s | allYeses s = [Yes []]
				  | containsYeses s = filterFromYeses2 s
				  | otherwise = s

filterFromYeses2 [] = []
filterFromYeses2 ((Yes []):ss) = filterFromYeses2 ss
filterFromYeses2 ((Yes s):ss) = ((Yes s):(filterFromYeses2 ss))

allYeses [] = True
allYeses ((Yes []):ss) = True && allYeses ss
allYeses ((Yes s):ss) = False

containsYeses [] = False
containsYeses ((Yes []):ss) = True 
containsYeses ((Yes s):ss) = False || containsYeses ss