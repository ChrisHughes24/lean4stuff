import Stuff.normalizing_properly.prod_coprod_vars1

open prod_coprod prod_coprod.syn

def U : prod_coprod := Ovar "U"
def V : prod_coprod := Ovar "V"
def W : prod_coprod := Ovar "W"
def X : prod_coprod := Ovar "X"
def Y : prod_coprod := Ovar "Y"
def Z : prod_coprod := Ovar "Z"

def uu : syn U U := var "uu"
def uv : syn U V := var "uv"
def uw : syn U W := var "uw"
def ux : syn U X := var "ux"
def uy : syn U Y := var "uy"
def uz : syn U Z := var "uz"

def vu : syn V U := var "vu"
def vv : syn V V := var "vv"
def vw : syn V W := var "vw"
def vx : syn V X := var "vx"
def vy : syn V Y := var "vy"
def vz : syn V Z := var "vz"

def wu : syn W U := var "wu"
def wv : syn W V := var "wv"
def ww : syn W W := var "ww"
def wx : syn W X := var "wx"
def wy : syn W Y := var "wy"
def wz : syn W Z := var "wz"

def xu : syn X U := var "xu"
def xv : syn X V := var "xv"
def xw : syn X W := var "xw"
def xx : syn X X := var "xx"
def xy : syn X Y := var "xy"
def xz : syn X Z := var "xz"

def yu : syn Y U := var "yu"
def yv : syn Y V := var "yv"
def yw : syn Y W := var "yw"
def yx : syn Y X := var "yx"
def yy : syn Y Y := var "yy"
def yz : syn Y Z := var "yz"

def zu : syn Z U := var "zu"
def zv : syn Z V := var "zv"
def zw : syn Z W := var "zw"
def zx : syn Z X := var "zx"
def zy : syn Z Y := var "zy"
def zz : syn Z Z := var "zz"

def opObj : prod_coprod → prod_coprod
| Ovar X => Ovar X
| bot => top
| top => bot
| coprod X Y => prod (opObj X) (opObj Y)
| prod X Y => coprod (opObj X) (opObj Y)

def op : {X Y : prod_coprod} → syn X Y → syn (opObj Y) (opObj X)
| _, _, syn.var f => syn.var f
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

unsafe def bopeq {X Y : prod_coprod} (f g : syn X Y) : Bool :=
f.beq g && (op f).beq (op g)


mutual

unsafe def toString' : {X Y : prod_coprod} → syn2' X Y → String
| _, _, syn2'.id _ => ""
| _, _, syn2'.var f => f
| _, _, syn2'.prod_mk f g => "prod (" ++ toString f ++ ", " ++ toString g ++ ")"
| _, _, syn2'.coprod_mk f g => "coprod (" ++ toString f ++ ", " ++ toString g ++ ")"
| _, _, syn2'.comp_inl f => "comp_inl (" ++ toString f ++ ")"
| _, _, syn2'.comp_inr f => "comp_inr (" ++ toString f ++ ")"
| _, _, syn2'.fst_comp f => "fst_comp (" ++ toString f ++ ")"
| _, _, syn2'.snd_comp f => "snd_comp (" ++ toString f ++ ")"
| _, _, syn2'.top_mk _ => "top_mk"
| _, _, syn2'.bot_mk _ => "bot_mk"


unsafe def toString : {X Y : prod_coprod} → syn2 X Y → String
| _, _, syn2.of' f => toString' f
| _, _, syn2.comp' f g => toString f ++ ";" ++ toString' g

end

#eval bopeq
  ((prod_mk uv uw).comp fst)
  uv

#eval bopeq
  ((coprod_mk vu xu).comp ((prod_mk uv uw).comp (prod_mk (fst.comp vw) (snd.comp ww))))
  (coprod_mk (prod_mk (vu.comp (uv.comp vw)) ((vu.comp uw).comp ww))
            (prod_mk (xu.comp (uv.comp vw)) ((xu.comp uw).comp ww)))

#eval toString (syn2.normalize (syn2.of_syn
  ((coprod_mk vu xu).comp ((prod_mk uv uw).comp (prod_mk (fst.comp vw) (snd.comp ww))))))

#eval bopeq
  (comp inl ((coprod_mk vu xu).comp (((prod_mk uv uw).comp (prod_mk (fst.comp vw) (snd.comp ww))).comp snd)))
  (comp (comp inl (coprod_mk (prod_mk (vu.comp (uv.comp vw)) ((vu.comp uw).comp ww))
            (prod_mk (xu.comp (uv.comp vw)) ((xu.comp uw).comp ww)))) snd)

#eval bopeq
  (comp ((coprod_mk vu xu).comp ((prod_mk uv uw).comp (prod_mk (fst.comp vw) (snd.comp ww)))) fst)
  (comp (coprod_mk (prod_mk (vu.comp (uv.comp vw)) ((vu.comp uw).comp ww))
            (prod_mk (xu.comp (uv.comp vw)) ((xu.comp uw).comp ww))) fst)

#eval bopeq
  (comp ((coprod_mk vu xu).comp ((prod_mk uv uw).comp (prod_mk (fst.comp vw) (snd.comp ww)))) (@inr X _))
  (coprod_mk (comp (prod_mk (vu.comp (uv.comp vw)) ((vu.comp uw).comp ww)) inr)
            (comp (prod_mk (xu.comp (uv.comp vw)) ((xu.comp uw).comp ww)) inr))

#eval
  let p : syn top (coprod top X) := inl
  beq
    (coprod_mk p inr)
    (syn.id (coprod top X))
