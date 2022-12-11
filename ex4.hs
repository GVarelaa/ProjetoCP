import Cp
import LTree
import RelCalc
import Data.List
import List

rankings = [
 ("Argentina", 4.8),
 ("Australia", 4.0),
 ("Belgium", 5.0),
 ("Brazil", 5.0),
 ("Cameroon", 4.0),
 ("Canada", 4.0),
 ("Costa Rica", 4.1),
 ("Croatia", 4.4),
 ("Denmark", 4.5),
 ("Ecuador", 4.0),
 ("England", 4.7),
 ("France", 4.8),
 ("Germany", 4.5),
 ("Ghana", 3.8),
 ("Iran", 4.2),
 ("Japan", 4.2),
 ("Korea Republic", 4.2),
 ("Mexico", 4.5),
 ("Morocco", 4.2),
 ("Netherlands", 4.6),
 ("Poland", 4.2),
 ("Portugal", 4.6),
 ("Qatar", 3.9),
 ("Saudi Arabia", 3.9),
 ("Senegal", 4.3),
 ("Serbia", 4.2),
 ("Spain", 4.7),
 ("Switzerland", 4.4),
 ("Tunisia", 4.1),
 ("USA", 4.4),
 ("Uruguay", 4.5),
 ("Wales", 4.3)]

type Team = String
type Group = [Team]
type Match = (Team, Team)
groups :: [Group]
groups = [
 ["Qatar", "Ecuador", "Senegal", "Netherlands"],
 ["England", "Iran", "USA", "Wales"],
 ["Argentina", "Saudi Arabia", "Mexico", "Poland"],
 ["France", "Denmark", "Tunisia", "Australia"],
 ["Spain", "Germany", "Japan", "Costa Rica"],
 ["Belgium", "Canada", "Morocco", "Croatia"],
 ["Brazil", "Serbia", "Switzerland", "Cameroon"],
 ["Portugal", "Ghana", "Uruguay", "Korea Republic"]]

winner :: Team 
winner = wcup groups

wcup = knockoutStage . groupStage

knockoutStage = cataLTree (either id koCriteria)

rank x = 4 ** (pap rankings x - 3.8)

koCriteria = s . (split (id >< id) (rank >< rank)) where
    s ((s1 , s2 ), (r1 , r2 )) = let d = r1 - r2 in
        if d == 0 then s1
        else if d > 0 then s1 else s2

groupStage :: [Group] -> LTree Team
groupStage = initKnockoutStage . simulateGroupStage . genGroupStageMatches

genGroupStageMatches :: [Group] -> [[Match]]
genGroupStageMatches = map generateMatches

generateMatches :: [Team] -> [Match]
generateMatches = pairup

-- TODO
pairup :: Eq b => [b] -> [(b,b)]
pairup = undefined

gsCriteria :: Match -> Maybe Team
gsCriteria = s . (split (id >< id) (rank >< rank)) where
    s ((s1 , s2 ), (r1 , r2 )) = let d = r1 - r2 in
        if d > 0.5 then Just s1
        else if d < -0.5 then Just s2
        else Nothing

simulateGroupStage :: [[Match]] -> [[Team]]
simulateGroupStage = map (groupWinners gsCriteria)

best n = map p1 . take n . reverse . presort p2

collect :: (Eq a, Eq b) => [(a, b)] -> [(a, [b])]
collect x = nub [ k |-> [ d' | (k',d') <- x , k'==k ] | (k,d) <- x ]


-- TODO
consolidate :: (Num d, Eq d, Eq b) => [(b, d)] -> [(b, d)]
consolidate = map (id >< sum) . Main.collect

groupWinners criteria = best 2 . consolidate . (>>=matchResult criteria)

-- TODO
matchResult :: (Match -> Maybe Team) -> Match -> [(Team, Int)]
matchResult = undefined

initKnockoutStage = anaLTree(glt) . arrangement
    where glt = undefined

arrangement = (>>=swapTeams) . chunksOf 4 where
    swapTeams [[a1 , a2 ], [b1 , b2 ], [c1 , c2 ], [d1 , d2 ]] = [a1 , b2 , c1 , d2 , b1 , a2 , d1 , c2 ]

