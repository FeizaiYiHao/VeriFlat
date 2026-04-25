use vstd::prelude::*;
use crate::*;
verus! {


pub ghost struct UserViewValue<T, const HasKillState: bool>{
    pub value: T,
    pub killed: bool,
}

impl<T, const HasKillState: bool> UserViewValue<T, HasKillState>{
    pub open spec fn view(&self) -> T{
        self.value
    }

    pub open spec fn from(value: T, killed: bool) -> Self{
        Self { value: value, killed: killed }
    }
}

impl<T> UserViewValue<T, true>{
    pub open spec fn killed(&self) -> bool{
        self.killed
    }
}


}
