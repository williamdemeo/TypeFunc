
open import Preliminaries

module lecture.ExtrinsicBoth where

  module RBT (Key : Set) (compare : Key -> Key -> Order) (Value : Set) where 

    -- ----------------------------------------------------------------------
    -- the code

    data Color : Set where
      Red : Color
      Black : Color

    data Tree : Set where
      Empty : Tree
      Node : (l : Tree) -> (c : Color) → (kv : Key × Value) -> (r : Tree) -> Tree

    data BalanceView : Set where
       Violation : Tree → (Key × Value) → Tree → (Key × Value) → Tree → (Key × Value) → Tree → BalanceView
       OK : Tree → Color → Key × Value → Tree -> BalanceView

    view : Tree → Color → (Key × Value) → Tree → BalanceView
    view (Node (Node a Red x b) Red y c) Black z d =  
            Violation a x b y c z d
    view (Node a Red x (Node b Red y c)) Black z d = 
            Violation a x b y c z d
    view a Black x (Node (Node b Red y c) Red z d) = 
            Violation a x b y c z d
    view a Black x (Node b Red y (Node c Red z d)) =
            Violation a x b y c z d
    view l co kv r = OK l co kv r

    balance : Tree → (c : Color) (kv : (Key × Value)) → Tree → Tree
    balance l co kv r with view l co kv r 
    ... | Violation a x b y c z d =
            Node (Node a Black x b) Red y (Node c Black z d)
    ... | OK l' co' kv' r' = Node l' co' kv' r'

    ins : Tree -> (Key × Value) -> Tree
    ins Empty kv = Node Empty Red kv Empty
    ins (Node l c (k' , v') r) (k , v) with compare k k'
    ... | Equal = Node l c (k , v) r
    ... | Less = balance (ins l (k , v)) c (k' , v') r
    ... | Greater = balance l c (k' , v') (ins r (k , v))

    blackenRoot : Tree → Tree
    blackenRoot Empty = Empty
    blackenRoot (Node l _ kv r) = Node l Black kv r

    insert : Tree -> Key × Value -> Tree
    insert t kv = blackenRoot (ins t kv)

    -- ----------------------------------------------------------------------
    -- correctness of the view

    data RootColored : Tree -> Color -> Set where
      RC-Empty : RootColored Empty Black
      RC-Red   : {l : Tree} {kv : Key × Value} {r : Tree} → RootColored (Node l Red kv r) Red
      RC-Black : {l : Tree} {kv : Key × Value} {r : Tree} → RootColored (Node l Black kv r) Black

    data ViolationType (a : Tree) (x : Key × Value) (b : Tree) (y : Key × Value) (c : Tree) (z : Key × Value) (d : Tree) :
                       Tree → Color → Key × Value → Tree → Set where
      Violation1 : ViolationType a x b y c z d (Node (Node a Red x b) Red y c) Black z d
      Violation2 : ViolationType a x b y c z d (Node a Red x (Node b Red y c)) Black z d
      Violation3 : ViolationType a x b y c z d a Black x (Node (Node b Red y c) Red z d)
      Violation4 : ViolationType a x b y c z d a Black x (Node b Red y (Node c Red z d))

    -- no red/red violation at the root 
    data RootOK : Tree → Set where
      ROK-Empty : RootOK Empty
      ROK-Black : {l : Tree} {kv : Key × Value} {r : Tree} → RootOK (Node l Black kv r)
      ROK-Red : {l : Tree} {kv : Key × Value} {r : Tree} → RootColored l Black → RootColored r Black 
                → RootOK (Node l Red kv r)

    data ViewInvariant : (l : Tree) (co : Color) (kv : Key × Value) (r : Tree) → BalanceView → Set where
      ViolationInv : ∀ {l co kv r a x b y c z d} → ViolationType a x b y c z d l co kv r → ViewInvariant l co kv r (Violation a x b y c z d)
      OKBlackInv : ∀ {l kv r} → RootOK l → RootOK r → ViewInvariant l Black kv r (OK l Black kv r)
      OKRedInv   : ∀ {l kv r} → ViewInvariant l Red kv r (OK l Red kv r) 

    -- not Agda's finest hour
    view-ok : (l : Tree) (co : Color) (kv : Key × Value) (r : Tree) → ViewInvariant l co kv r (view l co kv r)
    view-ok Empty Red kv r = OKRedInv
    view-ok (Node Empty Red kv Empty) Red kv' r' = OKRedInv
    view-ok (Node Empty Red kv (Node l Red kv' r)) Red kv0 r' = OKRedInv
    view-ok (Node Empty Red kv (Node l Black kv' r)) Red kv0 r' = OKRedInv
    view-ok (Node Empty Black kv r) Red kv' r' = OKRedInv
    view-ok (Node (Node l Red kv r) Red kv' Empty) Red kv0 r0 = OKRedInv
    view-ok (Node (Node l Black kv r) Red kv' Empty) Red kv0 r0 = OKRedInv
    view-ok (Node (Node l Red kv r) Red kv' (Node l' Red kv0 r')) Red kv1 r0 = OKRedInv
    view-ok (Node (Node l Red kv r) Red kv' (Node l' Black kv0 r')) Red kv1 r0 = OKRedInv
    view-ok (Node (Node l Black kv r) Red kv' (Node l' Red kv0 r')) Red kv1 r0 = OKRedInv
    view-ok (Node (Node l Black kv r) Red kv' (Node l' Black kv0 r')) Red kv1 r0 = OKRedInv
    view-ok (Node (Node l Red kv r) Black kv' r') Red kv0 r0 = OKRedInv
    view-ok (Node (Node l Black kv r) Black kv' r') Red kv0 r0 = OKRedInv
    view-ok Empty Black kv Empty = OKBlackInv ROK-Empty ROK-Empty
    view-ok Empty Black kv (Node Empty Red kv' Empty) = OKBlackInv ROK-Empty (ROK-Red RC-Empty RC-Empty)
    view-ok Empty Black kv (Node Empty Red kv' (Node l Red kv0 r)) = ViolationInv Violation4
    view-ok Empty Black kv (Node Empty Red kv' (Node l Black kv0 r)) = OKBlackInv ROK-Empty (ROK-Red RC-Empty RC-Black)
    view-ok Empty Black kv (Node Empty Black kv' r) = OKBlackInv ROK-Empty ROK-Black
    view-ok Empty Black kv (Node (Node l Red kv' r) Red kv0 r') = ViolationInv Violation3
    view-ok Empty Black kv (Node (Node l Red kv' r) Black kv0 r') = OKBlackInv ROK-Empty ROK-Black
    view-ok Empty Black kv (Node (Node l Black kv' r) Red kv0 Empty) = OKBlackInv ROK-Empty (ROK-Red RC-Black RC-Empty)
    view-ok Empty Black kv (Node (Node l Black kv' r) Red kv0 (Node l' Red kv1 r')) = ViolationInv Violation4
    view-ok Empty Black kv (Node (Node l Black kv' r) Red kv0 (Node l' Black kv1 r')) = OKBlackInv ROK-Empty (ROK-Red RC-Black RC-Black)
    view-ok Empty Black kv (Node (Node l Black kv' r) Black kv0 r') = OKBlackInv ROK-Empty ROK-Black
    view-ok (Node Empty Black kv Empty) Black kv' Empty = OKBlackInv ROK-Black ROK-Empty
    view-ok (Node Empty Black kv Empty) Black kv' (Node Empty Red kv0 Empty) = OKBlackInv ROK-Black (ROK-Red RC-Empty RC-Empty)
    view-ok (Node Empty Black kv Empty) Black kv' (Node Empty Red kv0 (Node l Red kv1 r)) = ViolationInv Violation4
    view-ok (Node Empty Black kv Empty) Black kv' (Node Empty Red kv0 (Node l Black kv1 r)) = OKBlackInv ROK-Black (ROK-Red RC-Empty RC-Black)
    view-ok (Node Empty Black kv Empty) Black kv' (Node (Node l Red kv0 r) Red kv1 r') = ViolationInv Violation3
    view-ok (Node Empty Black kv Empty) Black kv' (Node (Node l Black kv0 r) Red kv1 Empty) = OKBlackInv ROK-Black (ROK-Red RC-Black RC-Empty)
    view-ok (Node Empty Black kv Empty) Black kv' (Node (Node l Black kv0 r) Red kv1 (Node l' Red kv2 r')) = ViolationInv Violation4
    view-ok (Node Empty Black kv Empty) Black kv' (Node (Node l Black kv0 r) Red kv1 (Node l' Black kv2 r')) = OKBlackInv ROK-Black (ROK-Red RC-Black RC-Black)
    view-ok (Node Empty Black kv Empty) Black kv' (Node Empty Black kv0 Empty) = OKBlackInv ROK-Black ROK-Black
    view-ok (Node Empty Black kv Empty) Black kv' (Node (Node l Red kv0 r) Black kv1 Empty) = OKBlackInv ROK-Black ROK-Black
    view-ok (Node Empty Black kv Empty) Black kv' (Node (Node l Black kv0 r) Black kv1 Empty) = OKBlackInv ROK-Black ROK-Black
    view-ok (Node Empty Black kv Empty) Black kv' (Node Empty Black kv0 (Node l' Red kv1 r)) = OKBlackInv ROK-Black ROK-Black
    view-ok (Node Empty Black kv Empty) Black kv' (Node (Node l Red kv0 r) Black kv1 (Node l' Red kv2 r')) = OKBlackInv ROK-Black ROK-Black
    view-ok (Node Empty Black kv Empty) Black kv' (Node (Node l Black kv0 r) Black kv1 (Node l' Red kv2 r')) = OKBlackInv ROK-Black ROK-Black
    view-ok (Node Empty Black kv Empty) Black kv' (Node Empty Black kv0 (Node l' Black kv1 r)) = OKBlackInv ROK-Black ROK-Black
    view-ok (Node Empty Black kv Empty) Black kv' (Node (Node l Red kv0 r) Black kv1 (Node l' Black kv2 r')) = OKBlackInv ROK-Black ROK-Black
    view-ok (Node Empty Black kv Empty) Black kv' (Node (Node l Black kv0 r) Black kv1 (Node l' Black kv2 r')) = OKBlackInv ROK-Black ROK-Black
    view-ok (Node Empty Black kv (Node l Red kv' r)) Black kv0 Empty = OKBlackInv ROK-Black ROK-Empty
    view-ok (Node Empty Black kv (Node l Red kv' r)) Black kv0 (Node Empty Red kv1 Empty) = OKBlackInv ROK-Black (ROK-Red RC-Empty RC-Empty)
    view-ok (Node Empty Black kv (Node l Red kv' r)) Black kv0 (Node Empty Red kv1 (Node l' Red kv2 r')) = ViolationInv Violation4
    view-ok (Node Empty Black kv (Node l Red kv' r)) Black kv0 (Node Empty Red kv1 (Node l' Black kv2 r')) = OKBlackInv ROK-Black (ROK-Red RC-Empty RC-Black)
    view-ok (Node Empty Black kv (Node l Red kv' r)) Black kv0 (Node Empty Black kv1 Empty) = OKBlackInv ROK-Black ROK-Black
    view-ok (Node Empty Black kv (Node l Red kv' r)) Black kv0 (Node Empty Black kv1 (Node l' c kv2 r')) = OKBlackInv ROK-Black ROK-Black
    view-ok (Node Empty Black kv (Node l Red kv' r)) Black kv0 (Node (Node l' Red kv1 r') Red kv2 r0) = ViolationInv Violation3
    view-ok (Node Empty Black kv (Node l Red kv' r)) Black kv0 (Node (Node l' Red kv1 r') Black kv2 r0) = OKBlackInv ROK-Black ROK-Black
    view-ok (Node Empty Black kv (Node l Red kv' r)) Black kv0 (Node (Node l' Black kv1 r') Red kv2 Empty) = OKBlackInv ROK-Black (ROK-Red RC-Black RC-Empty)
    view-ok (Node Empty Black kv (Node l Red kv' r)) Black kv0 (Node (Node l' Black kv1 r') Red kv2 (Node l0 Red kv3 r0)) = ViolationInv Violation4
    view-ok (Node Empty Black kv (Node l Red kv' r)) Black kv0 (Node (Node l' Black kv1 r') Red kv2 (Node l0 Black kv3 r0)) = OKBlackInv ROK-Black (ROK-Red RC-Black RC-Black)
    view-ok (Node Empty Black kv (Node l Red kv' r)) Black kv0 (Node (Node l' Black kv1 r') Black kv2 r0) = OKBlackInv ROK-Black ROK-Black
    view-ok (Node Empty Black kv (Node l Black kv' r)) Black kv0 Empty = OKBlackInv ROK-Black ROK-Empty
    view-ok (Node Empty Black kv (Node l Black kv' r)) Black kv0 (Node Empty Red kv1 Empty) = OKBlackInv ROK-Black (ROK-Red RC-Empty RC-Empty)
    view-ok (Node Empty Black kv (Node l Black kv' r)) Black kv0 (Node Empty Red kv1 (Node l' Red kv2 r')) = ViolationInv Violation4
    view-ok (Node Empty Black kv (Node l Black kv' r)) Black kv0 (Node Empty Red kv1 (Node l' Black kv2 r')) = OKBlackInv ROK-Black (ROK-Red RC-Empty RC-Black)
    view-ok (Node Empty Black kv (Node l Black kv' r)) Black kv0 (Node Empty Black kv1 r') = OKBlackInv ROK-Black ROK-Black
    view-ok (Node Empty Black kv (Node l Black kv' r)) Black kv0 (Node (Node l' Red kv1 r') Red kv2 r0) = ViolationInv Violation3
    view-ok (Node Empty Black kv (Node l Black kv' r)) Black kv0 (Node (Node l' Red kv1 r') Black kv2 r0) = OKBlackInv ROK-Black ROK-Black
    view-ok (Node Empty Black kv (Node l Black kv' r)) Black kv0 (Node (Node l' Black kv1 r') Red kv2 Empty) = OKBlackInv ROK-Black (ROK-Red RC-Black RC-Empty)
    view-ok (Node Empty Black kv (Node l Black kv' r)) Black kv0 (Node (Node l' Black kv1 r') Red kv2 (Node l0 Red kv3 r0)) = ViolationInv Violation4
    view-ok (Node Empty Black kv (Node l Black kv' r)) Black kv0 (Node (Node l' Black kv1 r') Red kv2 (Node l0 Black kv3 r0)) = OKBlackInv ROK-Black (ROK-Red RC-Black RC-Black)
    view-ok (Node Empty Black kv (Node l Black kv' r)) Black kv0 (Node (Node l' Black kv1 r') Black kv2 r0) = OKBlackInv ROK-Black ROK-Black
    view-ok (Node (Node l Red kv r) Black kv' r') Black kv0 Empty = OKBlackInv ROK-Black ROK-Empty                                                                            
    view-ok (Node (Node l Red kv r) Black kv' r') Black kv0 (Node Empty Red kv1 Empty) = OKBlackInv ROK-Black (ROK-Red RC-Empty RC-Empty)                                     
    view-ok (Node (Node l Red kv r) Black kv' r') Black kv0 (Node Empty Red kv1 (Node l' Red kv2 r0)) = ViolationInv Violation4                                               
    view-ok (Node (Node l Red kv r) Black kv' r') Black kv0 (Node Empty Red kv1 (Node l' Black kv2 r0)) = OKBlackInv ROK-Black (ROK-Red RC-Empty RC-Black)                    
    view-ok (Node (Node l Red kv r) Black kv' r') Black kv0 (Node Empty Black kv1 r0) = OKBlackInv ROK-Black ROK-Black                                                        
    view-ok (Node (Node l Red kv r) Black kv' r') Black kv0 (Node (Node l' Red kv1 r0) Red kv2 r1) = ViolationInv Violation3
    view-ok (Node (Node l Red kv r) Black kv' r') Black kv0 (Node (Node l' Black kv1 r0) Red kv2 Empty) = OKBlackInv ROK-Black (ROK-Red RC-Black RC-Empty)                    
    view-ok (Node (Node l Red kv r) Black kv' r') Black kv0 (Node (Node l' Black kv1 r0) Red kv2 (Node l0 Red kv3 r1)) = ViolationInv Violation4                              
    view-ok (Node (Node l Red kv r) Black kv' r') Black kv0 (Node (Node l' Black kv1 r0) Red kv2 (Node l0 Black kv3 r1)) = OKBlackInv ROK-Black (ROK-Red RC-Black RC-Black)   
    view-ok (Node (Node l Red kv r) Black kv' r') Black kv0 (Node (Node l' Red kv1 r0) Black kv2 r1) = OKBlackInv ROK-Black ROK-Black                                         
    view-ok (Node (Node l Red kv r) Black kv' r') Black kv0 (Node (Node l' Black kv1 r0) Black kv2 r1) = OKBlackInv ROK-Black ROK-Black                                       
    view-ok (Node (Node l Black kv r) Black kv' r') Black kv0 Empty = OKBlackInv ROK-Black ROK-Empty                                                                            
    view-ok (Node (Node l Black kv r) Black kv' r') Black kv0 (Node Empty Red kv1 Empty) = OKBlackInv ROK-Black (ROK-Red RC-Empty RC-Empty)                                     
    view-ok (Node (Node l Black kv r) Black kv' r') Black kv0 (Node Empty Red kv1 (Node l' Red kv2 r0)) = ViolationInv Violation4                                               
    view-ok (Node (Node l Black kv r) Black kv' r') Black kv0 (Node Empty Red kv1 (Node l' Black kv2 r0)) = OKBlackInv ROK-Black (ROK-Red RC-Empty RC-Black)                    
    view-ok (Node (Node l Black kv r) Black kv' r') Black kv0 (Node Empty Black kv1 r0) = OKBlackInv ROK-Black ROK-Black                                                        
    view-ok (Node (Node l Black kv r) Black kv' r') Black kv0 (Node (Node l' Red kv1 r0) Red kv2 r1) = ViolationInv Violation3                                                  
    view-ok (Node (Node l Black kv r) Black kv' r') Black kv0 (Node (Node l' Black kv1 r0) Red kv2 Empty) = OKBlackInv ROK-Black (ROK-Red RC-Black RC-Empty)                    
    view-ok (Node (Node l Black kv r) Black kv' r') Black kv0 (Node (Node l' Black kv1 r0) Red kv2 (Node l0 Red kv3 r1)) = ViolationInv Violation4                              
    view-ok (Node (Node l Black kv r) Black kv' r') Black kv0 (Node (Node l' Black kv1 r0) Red kv2 (Node l0 Black kv3 r1)) = OKBlackInv ROK-Black (ROK-Red RC-Black RC-Black)   
    view-ok (Node (Node l Black kv r) Black kv' r') Black kv0 (Node (Node l' Red kv1 r0) Black kv2 r1) = OKBlackInv ROK-Black ROK-Black                                         
    view-ok (Node (Node l Black kv r) Black kv' r') Black kv0 (Node (Node l' Black kv1 r0) Black kv2 r1) = OKBlackInv ROK-Black ROK-Black                                      
    view-ok (Node Empty Red kv (Node l Red kv' r)) Black kv0 r' = ViolationInv Violation2
    view-ok (Node Empty Red kv Empty) Black kv' Empty = OKBlackInv (ROK-Red RC-Empty RC-Empty) ROK-Empty                                                                             
    view-ok (Node Empty Red kv Empty) Black kv' (Node Empty Red kv1 Empty) = OKBlackInv (ROK-Red RC-Empty RC-Empty) (ROK-Red RC-Empty RC-Empty)                                      
    view-ok (Node Empty Red kv Empty) Black kv' (Node Empty Red kv1 (Node l' Red kv2 r0)) = ViolationInv Violation4                                                                  
    view-ok (Node Empty Red kv Empty) Black kv' (Node Empty Red kv1 (Node l' Black kv2 r0)) = OKBlackInv (ROK-Red RC-Empty RC-Empty) (ROK-Red RC-Empty RC-Black)                     
    view-ok (Node Empty Red kv Empty) Black kv' (Node Empty Black kv1 r0) = OKBlackInv (ROK-Red RC-Empty RC-Empty) ROK-Black                                                         
    view-ok (Node Empty Red kv Empty) Black kv' (Node (Node l' Red kv1 r0) Red kv2 r1) = ViolationInv Violation3                                                                     
    view-ok (Node Empty Red kv Empty) Black kv' (Node (Node l' Black kv1 r0) Red kv2 Empty) = OKBlackInv (ROK-Red RC-Empty RC-Empty) (ROK-Red RC-Black RC-Empty)                     
    view-ok (Node Empty Red kv Empty) Black kv' (Node (Node l' Black kv1 r0) Red kv2 (Node l0 Red kv3 r1)) = ViolationInv Violation4                                                 
    view-ok (Node Empty Red kv Empty) Black kv' (Node (Node l' Black kv1 r0) Red kv2 (Node l0 Black kv3 r1)) = OKBlackInv (ROK-Red RC-Empty RC-Empty) (ROK-Red RC-Black RC-Black)    
    view-ok (Node Empty Red kv Empty) Black kv' (Node (Node l' Red kv1 r0) Black kv2 r1) = OKBlackInv (ROK-Red RC-Empty RC-Empty) ROK-Black                                          
    view-ok (Node Empty Red kv Empty) Black kv' (Node (Node l' Black kv1 r0) Black kv2 r1) = OKBlackInv (ROK-Red RC-Empty RC-Empty) ROK-Black                                        
    view-ok (Node Empty Red kv (Node l Black kv' r)) Black kv0 Empty = OKBlackInv (ROK-Red RC-Empty RC-Black) ROK-Empty                                                                             
    view-ok (Node Empty Red kv (Node l Black kv' r)) Black kv0 (Node Empty Red kv1 Empty) = OKBlackInv (ROK-Red RC-Empty RC-Black) (ROK-Red RC-Empty RC-Empty)                                      
    view-ok (Node Empty Red kv (Node l Black kv' r)) Black kv0 (Node Empty Red kv1 (Node l' Red kv2 r0)) = ViolationInv Violation4                                                                  
    view-ok (Node Empty Red kv (Node l Black kv' r)) Black kv0 (Node Empty Red kv1 (Node l' Black kv2 r0)) = OKBlackInv (ROK-Red RC-Empty RC-Black) (ROK-Red RC-Empty RC-Black)                     
    view-ok (Node Empty Red kv (Node l Black kv' r)) Black kv0 (Node Empty Black kv1 r0) = OKBlackInv (ROK-Red RC-Empty RC-Black) ROK-Black                                                         
    view-ok (Node Empty Red kv (Node l Black kv' r)) Black kv0 (Node (Node l' Red kv1 r0) Red kv2 r1) = ViolationInv Violation3                                                                     
    view-ok (Node Empty Red kv (Node l Black kv' r)) Black kv0 (Node (Node l' Black kv1 r0) Red kv2 Empty) = OKBlackInv (ROK-Red RC-Empty RC-Black) (ROK-Red RC-Black RC-Empty)                     
    view-ok (Node Empty Red kv (Node l Black kv' r)) Black kv0 (Node (Node l' Black kv1 r0) Red kv2 (Node l0 Red kv3 r1)) = ViolationInv Violation4                                                 
    view-ok (Node Empty Red kv (Node l Black kv' r)) Black kv0 (Node (Node l' Black kv1 r0) Red kv2 (Node l0 Black kv3 r1)) = OKBlackInv (ROK-Red RC-Empty RC-Black) (ROK-Red RC-Black RC-Black)    
    view-ok (Node Empty Red kv (Node l Black kv' r)) Black kv0 (Node (Node l' Red kv1 r0) Black kv2 r1) = OKBlackInv (ROK-Red RC-Empty RC-Black) ROK-Black                                          
    view-ok (Node Empty Red kv (Node l Black kv' r)) Black kv0 (Node (Node l' Black kv1 r0) Black kv2 r1) = OKBlackInv (ROK-Red RC-Empty RC-Black) ROK-Black                                        
    view-ok (Node (Node l Red kv r) Red kv' r') Black kv0 r0 = ViolationInv Violation1
    view-ok (Node (Node l Black kv r) Red kv' Empty) Black kv0 Empty = OKBlackInv (ROK-Red RC-Black RC-Empty) ROK-Empty                                                                             
    view-ok (Node (Node l Black kv r) Red kv' Empty) Black kv0 (Node Empty Red kv1 Empty) = OKBlackInv (ROK-Red RC-Black RC-Empty) (ROK-Red RC-Empty RC-Empty)                                      
    view-ok (Node (Node l Black kv r) Red kv' Empty) Black kv0 (Node Empty Red kv1 (Node l' Red kv2 r0)) = ViolationInv Violation4                                                                  
    view-ok (Node (Node l Black kv r) Red kv' Empty) Black kv0 (Node Empty Red kv1 (Node l' Black kv2 r0)) = OKBlackInv (ROK-Red RC-Black RC-Empty) (ROK-Red RC-Empty RC-Black)                     
    view-ok (Node (Node l Black kv r) Red kv' Empty) Black kv0 (Node Empty Black kv1 r0) = OKBlackInv (ROK-Red RC-Black RC-Empty) ROK-Black                                                         
    view-ok (Node (Node l Black kv r) Red kv' Empty) Black kv0 (Node (Node l' Red kv1 r0) Red kv2 r1) = ViolationInv Violation3                                                                     
    view-ok (Node (Node l Black kv r) Red kv' Empty) Black kv0 (Node (Node l' Black kv1 r0) Red kv2 Empty) = OKBlackInv (ROK-Red RC-Black RC-Empty) (ROK-Red RC-Black RC-Empty)                     
    view-ok (Node (Node l Black kv r) Red kv' Empty) Black kv0 (Node (Node l' Black kv1 r0) Red kv2 (Node l0 Red kv3 r1)) = ViolationInv Violation4                                                 
    view-ok (Node (Node l Black kv r) Red kv' Empty) Black kv0 (Node (Node l' Black kv1 r0) Red kv2 (Node l0 Black kv3 r1)) = OKBlackInv (ROK-Red RC-Black RC-Empty) (ROK-Red RC-Black RC-Black)    
    view-ok (Node (Node l Black kv r) Red kv' Empty) Black kv0 (Node (Node l' Red kv1 r0) Black kv2 r1) = OKBlackInv (ROK-Red RC-Black RC-Empty) ROK-Black                                          
    view-ok (Node (Node l Black kv r) Red kv' Empty) Black kv0 (Node (Node l' Black kv1 r0) Black kv2 r1) = OKBlackInv (ROK-Red RC-Black RC-Empty) ROK-Black                                        
    view-ok (Node (Node l Black kv r) Red kv' (Node l' Red kv0 r')) Black kv1 r0 = ViolationInv Violation2
    view-ok (Node (Node l Black kv r) Red kv' (Node l' Black kv0 r')) Black kv1 Empty = OKBlackInv (ROK-Red RC-Black RC-Black) ROK-Empty                                                                             
    view-ok (Node (Node l Black kv r) Red kv' (Node l' Black kv0 r')) Black _ (Node Empty Red _ Empty) = OKBlackInv (ROK-Red RC-Black RC-Black) (ROK-Red RC-Empty RC-Empty)                                      
    view-ok (Node (Node l Black kv r) Red kv' (Node _ Black kv0 r')) Black _ (Node Empty Red _ (Node _ Red kv2 r0)) = ViolationInv Violation4                                                                  
    view-ok (Node (Node l Black kv r) Red kv' (Node _ Black kv0 r')) Black _ (Node Empty Red _ (Node _ Black kv2 r0)) = OKBlackInv (ROK-Red RC-Black RC-Black) (ROK-Red RC-Empty RC-Black)                     
    view-ok (Node (Node l Black kv r) Red kv' (Node _ Black kv0 r')) Black _ (Node Empty Black _ r0) = OKBlackInv (ROK-Red RC-Black RC-Black) ROK-Black                                                         
    view-ok (Node (Node l Black kv r) Red kv' (Node _ Black kv0 r')) Black _ (Node (Node _ Red _ r0) Red kv2 r1) = ViolationInv Violation3                                                                     
    view-ok (Node (Node l Black kv r) Red kv' (Node _ Black kv0 r')) Black _ (Node (Node _ Black _ r0) Red kv2 Empty) = OKBlackInv (ROK-Red RC-Black RC-Black) (ROK-Red RC-Black RC-Empty)                     
    view-ok (Node (Node l Black kv r) Red kv' (Node _ Black kv0 r')) Black _ (Node (Node _ Black _ r0) Red kv2 (Node l0 Red kv3 r1)) = ViolationInv Violation4                                                 
    view-ok (Node (Node l Black kv r) Red kv' (Node _ Black kv0 r')) Black _ (Node (Node _ Black _ r0) Red kv2 (Node l0 Black kv3 r1)) = OKBlackInv (ROK-Red RC-Black RC-Black) (ROK-Red RC-Black RC-Black)    
    view-ok (Node (Node l Black kv r) Red kv' (Node _ Black kv0 r')) Black _ (Node (Node _ Red _ r0) Black kv2 r1) = OKBlackInv (ROK-Red RC-Black RC-Black) ROK-Black                                          
    view-ok (Node (Node l Black kv r) Red kv' (Node _ Black kv0 r')) Black _ (Node (Node _ Black _ r0) Black kv2 r1) = OKBlackInv (ROK-Red RC-Black RC-Black) ROK-Black                                        

    -- ----------------------------------------------------------------------
    -- black-height

    data ColorHeight : Color → Nat → Nat → Set where
      CH-Red   : {n : Nat} → ColorHeight Red n n
      CH-Black : {n : Nat} → ColorHeight Black n (S n)

    data HasBH : Tree -> Nat -> Set where
      HBH-Empty : HasBH Empty 1
      HBH-Node  : {n m : Nat} {c : Color} {l r : Tree} {kv : Key × Value}
                → HasBH l n 
                → ColorHeight c n m 
                → HasBH r n 
                → HasBH (Node l c kv r) m

    blackenRoot-bh : {t : Tree} {n : Nat} → HasBH t n → Σ \m → (HasBH (blackenRoot t) m)
    blackenRoot-bh HBH-Empty = _ , HBH-Empty
    blackenRoot-bh (HBH-Node hl ch hr) = _ , (HBH-Node hl CH-Black hr)

    -- good exercise for views
    balance-bh : {l : Tree} {c : Color} {kv : (Key × Value)} {r : Tree} {n m : Nat}
               → HasBH l n
               → ColorHeight c n m
               → HasBH r n
               → HasBH (balance l c kv r) m
    balance-bh {l}{c}{kv}{r}{n}{m} hl ch hr with view l c kv r | view-ok l c kv r 
    balance-bh (HBH-Node (HBH-Node ha CH-Red hb) CH-Red hc) CH-Black hd | ._ | ViolationInv Violation1 = HBH-Node (HBH-Node ha CH-Black hb) CH-Red (HBH-Node hc CH-Black hd)
    balance-bh (HBH-Node ha CH-Red (HBH-Node hb CH-Red hc)) CH-Black hd | ._ | ViolationInv Violation2 = HBH-Node (HBH-Node ha CH-Black hb) CH-Red (HBH-Node hc CH-Black hd)
    balance-bh ha CH-Black (HBH-Node (HBH-Node hb CH-Red hc) CH-Red hd) | ._ | ViolationInv Violation3 = HBH-Node (HBH-Node ha CH-Black hb) CH-Red (HBH-Node hc CH-Black hd)
    balance-bh ha CH-Black (HBH-Node hb CH-Red (HBH-Node hc CH-Red hd)) | ._ | ViolationInv Violation4 = HBH-Node (HBH-Node ha CH-Black hb) CH-Red (HBH-Node hc CH-Black hd)
    balance-bh {l} {.Black} {kv} {r} hl CH-Black hr | .(OK l Black kv r) | OKBlackInv rl rr = HBH-Node hl CH-Black hr
    balance-bh {l} {.Red} {kv} {r} hl CH-Red hr | .(OK l Red kv r) | OKRedInv = HBH-Node hl CH-Red hr

    ins-bh : {t : Tree} {kv : Key × Value} {n : Nat} → HasBH t n → HasBH (ins t kv) n
    ins-bh HBH-Empty = HBH-Node HBH-Empty CH-Red HBH-Empty
    ins-bh {._} {k , v} (HBH-Node {n}{m}{c}{l}{r}{k' , v'} hl ch hr) with compare k k'
    ... | Less = balance-bh (ins-bh hl) ch hr 
    ... | Equal = HBH-Node hl ch hr
    ... | Greater = balance-bh hl ch (ins-bh hr)

    insert-bh : {n : Nat} {t : Tree} {kv : (Key × Value)}
              → HasBH t n
              → Σ \ m -> (HasBH (insert t kv) m)
    insert-bh h = blackenRoot-bh (ins-bh h)

    -- ----------------------------------------------------------------------
    -- well-red

    data WellRed : Tree -> Set where
      WR-Empty : WellRed Empty
      WR-Red   : {l : Tree} {kv : Key × Value} {r : Tree}
               → WellRed l
               → WellRed r
               → RootColored l Black
               → RootColored r Black
               → WellRed (Node l Red kv r)
      WR-Black : {l : Tree} {kv : Key × Value} {r : Tree}
               → WellRed l
               → WellRed r
               → WellRed (Node l Black kv r)

    data AlmostWellRed : Tree -> Set where
      AWR-Empty : AlmostWellRed Empty
      AWR-Node  : {l : Tree} {kv : Key × Value} {r : Tree} {c : Color}
                → WellRed l
                → WellRed r
                → AlmostWellRed (Node l c kv r)
 
    combine : {t : Tree} → RootOK t → AlmostWellRed t → WellRed t
    combine ROK-Empty a = WR-Empty
    combine ROK-Black (AWR-Node wl wr) = WR-Black wl wr
    combine (ROK-Red rl rr) (AWR-Node wl wr) = WR-Red wl wr rl rr

    -- ENH factor subsidiary case analysis into lemma?
    balance-fix-left : (l : Tree) (kv : Key × Value) (r : Tree)
                 → AlmostWellRed l 
                 → WellRed r 
                 → WellRed (balance l Black kv r)
    balance-fix-left l kv r al wr with view l Black kv r | view-ok l Black kv r  
    balance-fix-left .(Node (Node a Red x b) Red y c) .z .d (AWR-Node (WR-Red wa wb ca cb) wc) wd | Violation a x b y c z d | ViolationInv Violation1 = WR-Red (WR-Black wa wb) (WR-Black wc wd) RC-Black RC-Black
    balance-fix-left .(Node a Red x (Node b Red y c)) .z .d (AWR-Node wa (WR-Red wb wc rb rc)) wd | Violation a x b y c z d | ViolationInv Violation2 = WR-Red (WR-Black wa wb) (WR-Black wc wd) RC-Black RC-Black
    balance-fix-left .a .x .(Node (Node b Red y c) Red z d) al (WR-Red _ _ () _) | Violation a x b y c z d | ViolationInv Violation3 
    balance-fix-left .a .x .(Node b Red y (Node c Red z d)) al (WR-Red _ _ _ ()) | Violation a x b y c z d | ViolationInv Violation4 
    ... | .(OK l Black kv r) | OKBlackInv rl _ = WR-Black (combine rl al) wr

    balance-fix-right : (l : Tree) (kv : Key × Value) (r : Tree)
                 → WellRed l 
                 → AlmostWellRed r 
                 → WellRed (balance l Black kv r)
    balance-fix-right l kv r wl ar with view l Black kv r | view-ok l Black kv r 
    balance-fix-right .(Node (Node a Red x b) Red y c) z d (WR-Red _ _ () _) ad | .(Violation a x b y c z d) | ViolationInv {.(Node (Node a Red x b) Red y c)} {.Black} {.z} {.d} {a} {x} {b} {y} {c} Violation1
    balance-fix-right .(Node a Red x (Node b Red y c)) z d (WR-Red _ _ _ ()) ar | .(Violation a x b y c z d) | ViolationInv {.(Node a Red x (Node b Red y c))} {.Black} {.z} {.d} {a} {x} {b} {y} {c} Violation2
    balance-fix-right a x .(Node (Node b Red y c) Red z d) wa (AWR-Node (WR-Red wb wc rb rc) wd) | .(Violation a x b y c z d) | ViolationInv {.a} {.Black} {.x} {.(Node (Node b Red y c) Red z d)} {.a} {.x} {b} {y} {c} {z} {d} Violation3 = WR-Red (WR-Black wa wb) (WR-Black wc wd) RC-Black RC-Black
    balance-fix-right a x .(Node b Red y (Node c Red z d)) wa (AWR-Node wb (WR-Red wc wd rc rd)) | .(Violation a x b y c z d) | ViolationInv {.a} {.Black} {.x} {.(Node b Red y (Node c Red z d))} {.a} {.x} {b} {y} {c} {z} {d} Violation4 = WR-Red (WR-Black wa wb) (WR-Black wc wd) RC-Black RC-Black
    balance-fix-right l kv r wl ar | .(OK l Black kv r) | OKBlackInv _ rr = WR-Black wl (combine rr ar)
 
    balance-break : (l : Tree) (kv : Key × Value) (r : Tree)
                 → WellRed l 
                 → WellRed r 
                 → AlmostWellRed (balance l Red kv r)
    balance-break l kv r wl wr with view l Red kv r | view-ok l Red kv r 
    balance-break l kv r wl wr | .(Violation a x b y c z d) | ViolationInv {.l} {.Red} {.kv} {.r} {a} {x} {b} {y} {c} {z} {d} ()
    balance-break l kv r wl wr | .(OK l Red kv r) | OKRedInv = AWR-Node wl wr

    decide-root : (t : Tree) → Either (RootColored t Black) (RootColored t Red)
    decide-root Empty = Inl RC-Empty
    decide-root (Node _ Red _ _ ) = Inr RC-Red
    decide-root (Node _ Black _ _ ) = Inl RC-Black

    forget : {t : Tree} → WellRed t -> AlmostWellRed t
    forget WR-Empty = AWR-Empty
    forget (WR-Red wl wr _ _) = AWR-Node wl wr
    forget (WR-Black wl wr) = AWR-Node wl wr

    mutual
      ins-red : (t : Tree) (kv : Key × Value) → RootColored t Red → WellRed t → AlmostWellRed (ins t kv)
      ins-red .Empty kv rc WR-Empty = AWR-Node WR-Empty WR-Empty
      ins-red .(Node l Black kv' r) kv () (WR-Black {l} {kv'} {r} y y')
      ins-red .(Node l Red (k' , v') r) (k , v) rc (WR-Red {l} {k' , v'} {r} wl wr rl rr) with compare k k'
      ... | Less = balance-break (ins l (k , v)) (k' , v') r (ins-black l (k , v) rl wl) wr
      ... | Equal = AWR-Node wl wr
      ... | Greater = balance-break l (k' , v') (ins r (k , v)) wl (ins-black r (k , v) rr wr)
  
      ins-black : (t : Tree) (kv : Key × Value) → RootColored t Black → WellRed t → WellRed (ins t kv)
      ins-black .Empty kv rt WR-Empty = WR-Red WR-Empty WR-Empty RC-Empty RC-Empty
      ins-black .(Node l Red kv' r) kv () (WR-Red {l} {kv'} {r} y y' y0 y1)
      ins-black .(Node l Black (k' , v') r) (k , v) rt (WR-Black {l} {k' , v'} {r} wl wr) with compare k k'
      ... | Less = balance-fix-left (ins l (k , v)) (k' , v') r (ins-any l (k , v) wl) wr
      ... | Equal = WR-Black wl wr
      ... | Greater = balance-fix-right l (k' , v') (ins r (k , v)) wl (ins-any r (k , v) wr)

      ins-any : (t : Tree) (kv : Key × Value) → WellRed t -> AlmostWellRed (ins t kv)
      ins-any t kv wt with decide-root t 
      ... | Inl rt = forget (ins-black t kv rt wt)
      ... | Inr rt = ins-red t kv rt wt

    blackenRoot-fix : {t : Tree} → AlmostWellRed t → WellRed (blackenRoot t)
    blackenRoot-fix AWR-Empty = WR-Empty
    blackenRoot-fix (AWR-Node wl wr) = WR-Black wl wr

    insert-wellred : {t : Tree} {kv : Key × Value} 
                   -> WellRed t
                   -> WellRed (insert t kv)
    insert-wellred w = blackenRoot-fix (ins-any _ _ w)


  module Test where
    open RBT Nat Nat.compare Unit public

    t1 = insert (insert (insert (insert Empty (3 , <>)) (2 , <>)) (1 , <>)) (5 , <>)

    t2 = RBT.Node (Node Empty Black (2 , <>) Empty) Red (3 , <>) (Node Empty Black (4 , <>) Empty)
    t3 = ins t2 (1 , <>)
    t4 = ins t3 (0 , <>)
    