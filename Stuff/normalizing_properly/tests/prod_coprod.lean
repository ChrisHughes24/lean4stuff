import Stuff.normalizing_properly.prod_coprod
import Stuff.normalizing_properly.free_category

open free_cat
open prod_coprod prod_coprod.syn2

#eval (normalize (of_cat (mh ⟨"X"⟩ ⟨"Y"⟩ "f")) =
(normalize (of_cat (mh ⟨"X"⟩ ⟨"Y"⟩ "f")))