import Cp
import Nat

fbl a b c = p1.p1 . (for (split (split (p2.p1) p2) aux) ((0,1),1))
    where aux = (uncurry (+)) . ((uncurry (+)) >< id) . ((((c*) >< (b*))) >< (a*))

f a b c 0 = 0
f a b c 1 = 1
f a b c 2 = 1
f a b c n = a*(f a b c (n-1)) + b*(f a b c (n-2)) + c*(f a b c (n-3))