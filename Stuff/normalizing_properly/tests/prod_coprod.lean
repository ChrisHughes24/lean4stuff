import Stuff.normalizing_properly.prod_coprod
import Stuff.normalizing_properly.free_category

open free_cat
open prod_coprod prod_coprod.syn2

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

def uu : syn U U := syn.of_cat (mh _ _ "uv")
def uv : syn U V := syn.of_cat (mh _ _ "uv")
def uw : syn U W := syn.of_cat (mh _ _ "uw")
def ux : syn U X := syn.of_cat (mh _ _ "ux")
def uy : syn U Y := syn.of_cat (mh _ _ "uy")
def uz : syn U Z := syn.of_cat (mh _ _ "uz")

def uu : syn U U := syn.of_cat (mh _ _ "uv")
def uv : syn U V := syn.of_cat (mh _ _ "uv")
def uw : syn U W := syn.of_cat (mh _ _ "uw")
def ux : syn U X := syn.of_cat (mh _ _ "ux")
def uy : syn U Y := syn.of_cat (mh _ _ "uy")
def uz : syn U Z := syn.of_cat (mh _ _ "uz")

def uu : syn U U := syn.of_cat (mh _ _ "uv")
def uv : syn U V := syn.of_cat (mh _ _ "uv")
def uw : syn U W := syn.of_cat (mh _ _ "uw")
def ux : syn U X := syn.of_cat (mh _ _ "ux")
def uy : syn U Y := syn.of_cat (mh _ _ "uy")
def uz : syn U Z := syn.of_cat (mh _ _ "uz")

def b : syn Y Z := syn
