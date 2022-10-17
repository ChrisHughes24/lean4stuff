import Stuff.normalizing_properly.prod_coprod
import Stuff.normalizing_properly.free_category

open free_cat
open prod_coprod prod_coprod.syn

def U : prod_coprod free_cat := of_cat' ⟨"U"⟩
def V : prod_coprod free_cat := of_cat' ⟨"V"⟩
def W : prod_coprod free_cat := of_cat' ⟨"W"⟩
def X : prod_coprod free_cat := of_cat' ⟨"X"⟩
def Y : prod_coprod free_cat := of_cat' ⟨"Y"⟩
def Z : prod_coprod free_cat := of_cat' ⟨"Z"⟩

def uu : syn U U := syn.of_cat (mh _ _ "uu")
def uv : syn U V := syn.of_cat (mh _ _ "uv")
def uw : syn U W := syn.of_cat (mh _ _ "uw")
def ux : syn U X := syn.of_cat (mh _ _ "ux")
def uy : syn U Y := syn.of_cat (mh _ _ "uy")
def uz : syn U Z := syn.of_cat (mh _ _ "uz")

def vu : syn V U := syn.of_cat (mh _ _ "vu")
def vv : syn V V := syn.of_cat (mh _ _ "vv")
def vw : syn V W := syn.of_cat (mh _ _ "vw")
def vx : syn V X := syn.of_cat (mh _ _ "vx")
def vy : syn V Y := syn.of_cat (mh _ _ "vy")
def vz : syn V Z := syn.of_cat (mh _ _ "vz")

def wu : syn W U := syn.of_cat (mh _ _ "wu")
def wv : syn W V := syn.of_cat (mh _ _ "wv")
def ww : syn W W := syn.of_cat (mh _ _ "ww")
def wx : syn W X := syn.of_cat (mh _ _ "wx")
def wy : syn W Y := syn.of_cat (mh _ _ "wy")
def wz : syn W Z := syn.of_cat (mh _ _ "wz")

def xu : syn X U := syn.of_cat (mh _ _ "xu")
def xv : syn X V := syn.of_cat (mh _ _ "xv")
def xw : syn X W := syn.of_cat (mh _ _ "xw")
def xx : syn X X := syn.of_cat (mh _ _ "xx")
def xy : syn X Y := syn.of_cat (mh _ _ "xy")
def xz : syn X Z := syn.of_cat (mh _ _ "xz")

def yu : syn Y U := syn.of_cat (mh _ _ "yu")
def yv : syn Y V := syn.of_cat (mh _ _ "yv")
def yw : syn Y W := syn.of_cat (mh _ _ "yw")
def yx : syn Y X := syn.of_cat (mh _ _ "yx")
def yy : syn Y Y := syn.of_cat (mh _ _ "yy")
def yz : syn Y Z := syn.of_cat (mh _ _ "yz")

def zu : syn Z U := syn.of_cat (mh _ _ "zu")
def zv : syn Z V := syn.of_cat (mh _ _ "zv")
def zw : syn Z W := syn.of_cat (mh _ _ "zw")
def zx : syn Z X := syn.of_cat (mh _ _ "zx")
def zy : syn Z Y := syn.of_cat (mh _ _ "zy")
def zz : syn Z Z := syn.of_cat (mh _ _ "zz")

def opObj : prod_coprod free_cat → prod_coprod free_cat
| of_cat' X => of_cat' X
| bot => top
| top => bot
| coprod X Y => prod (opObj X) (opObj Y)
| prod X Y => coprod (opObj X) (opObj Y)

def free_cat.hom.op : {X Y : free_cat} → free_cat.hom X Y → free_cat.hom Y X
| _, _, free_cat.hom.id _ => free_cat.hom.id _
| _, _, free_cat.hom.comp' _ _ _ f g =>
free_cat.hom.comp (free_cat.hom.comp' _ _ _ (free_cat.hom.id _) g) (free_cat.hom.op f)

def op : {X Y : prod_coprod free_cat} → syn X Y → syn (opObj Y) (opObj X)
| _, _, syn.of_cat f => syn.of_cat f.op
| _, _, syn.comp f g => syn.comp (op g) (op f)
| _, _, syn.id _ => syn.id _
| _, _, syn.inl => syn.fst
| _, _, syn.inr => syn.snd
| _, _, syn.fst => syn.inl
| _, _, syn.snd => syn.inr
| _, _, syn.bot_mk _ => syn.top_mk _
| _, _, syn.top_mk _ => syn.bot_mk _
| _, _, syn.prod_mk f g => syn.coprod_mk (op f) (op g)
| _, _, syn.coprod_mk f g => syn.prod_mk (op f) (op g)

unsafe def bopeq {X Y : prod_coprod free_cat} (f g : syn X Y) : Bool :=
f.beq g && (op f).beq (op g)

#eval bopeq
  ((prod_mk uv uw).comp fst)
  uv

#eval bopeq
  ((coprod_mk vu xu).comp ((prod_mk uv uw).comp (prod_mk (fst.comp vw) (snd.comp ww))))
  (coprod_mk (prod_mk (vu.comp (uv.comp vw)) ((vu.comp uw).comp ww))
            (prod_mk (xu.comp (uv.comp vw)) ((xu.comp uw).comp ww)))

#eval bopeq
  (comp inl ((coprod_mk vu xu).comp (((prod_mk uv uw).comp (prod_mk (fst.comp vw) (snd.comp ww))).comp snd)))
  (comp (comp inl (coprod_mk (prod_mk (vu.comp (uv.comp vw)) ((vu.comp uw).comp ww))
            (prod_mk (xu.comp (uv.comp vw)) ((xu.comp uw).comp ww)))) snd)

#eval bopeq
  (comp ((coprod_mk vu xu).comp ((prod_mk uv uw).comp (prod_mk (fst.comp vw) (snd.comp ww)))) fst)
  (comp (coprod_mk (prod_mk (vu.comp (uv.comp vw)) ((vu.comp uw).comp ww))
            (prod_mk (xu.comp (uv.comp vw)) ((xu.comp uw).comp ww))) fst)

#eval bopeq
  (comp ((coprod_mk vu xu).comp ((prod_mk uv uw).comp (prod_mk (fst.comp vw) (snd.comp ww)))) (@inr _ _ X _))
  (comp (coprod_mk (comp (prod_mk (vu.comp (uv.comp vw)) ((vu.comp uw).comp ww)) inr)
            (comp (prod_mk (xu.comp (uv.comp vw)) ((xu.comp uw).comp ww)) inr)) (syn.id _))

#eval
  let p : syn top (coprod top X) := inl
  bopeq
    (coprod_mk p inr)
    (syn.id _)
