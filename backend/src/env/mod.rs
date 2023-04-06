use std::{
  collections::HashMap,
  rc::Rc,
  cell::RefCell,
};
use lispers_common::Symbol;
use crate::data::Value;

mod primitives;
mod default;
pub use default::default_env;

pub struct Env<S: Symbol> {
  parent: Option<Rc<RefCell<Env<S>>>>,
  values: HashMap<S, Value<S>>,
}

impl<S: Symbol> Env<S> {
  pub fn new() -> Self {
    Self {
      parent: None,
      values: HashMap::new(),
    }
  }

  pub fn extend(parent: Rc<RefCell<Env<S>>>) -> Self {
    Self {
      parent: Some(parent),
      values: HashMap::new(),
    }
  }

  pub fn define(&mut self, symbol: S, value: Value<S>) {
    self.values.insert(symbol, value);
  }

  pub fn undefine(&mut self, symbol: S) {
    if self.values.contains_key(&symbol) {
      self.values.remove(&symbol);
    }
    else if let Some(parent) = &self.parent {
      parent.borrow_mut().undefine(symbol);
    }
  }

  pub fn get(&self, symbol: S) -> Option<Value<S>> {
    if let Some(val) = self.values.get(&symbol) {
      Some(val.clone())
    }
    else if let Some(parent) = &self.parent {
      parent.borrow().get(symbol)
    }
    else {
      None
    }
  }

  pub fn set(&mut self, symbol: S, value: Value<S>) -> Result<(), S> {
    if self.values.contains_key(&symbol) {
      self.values.insert(symbol, value);
      Ok(())
    }
    else if let Some(parent) = &self.parent {
      parent.borrow_mut().set(symbol, value)
    }
    else {
      Err(symbol)
    }
  }

  fn intern_lookup(&self, symbol: S, depth: i64) -> (i64, i64) {
    if let Some(val) = self.values.get(&symbol) {
      match val {
        Value::Integer(val) => { (if let Some(_parent) = &self.parent {depth} else {-1}, *val) }
        _ => {(-1, 1)}
      }
    }
    else if let Some(parent) = &self.parent {
      parent.borrow().intern_lookup(symbol, depth + 1)
    }
    else {
      (-1, -1)
    }
  }
  pub fn lookup(&self, symbol: S) -> (i64, i64) {
    return self.intern_lookup(symbol, 0)
  }
  pub fn print(&self, msg: String) {
   println!("{} cte {:p} {}", msg, self, self.values.len());
  }
}

pub struct RTE<S: Symbol> {
  parent: Option<Rc<RefCell<RTE<S>>>>,
  pub values: Vec<Value<S>>,
//  #[cfg(Debug)] n: usize,
}

//static mut allo : usize = 0;
impl<S: Symbol> RTE<S> {
  pub fn up(&self) -> Rc<RefCell<RTE<S>>> {
    match &self.parent {
      None => RTE::new(),
      Some(parent) => parent.clone()
    }
  }

  pub fn new() -> Rc<RefCell<Self>> {
    Rc::new(RefCell::new(Self {
      parent: None,
      values: Vec::new(),
//#[cfg(Debug)] n: unsafe { let x=allo; allo=x+1; x}
    }))
  }

  pub fn extend(parent: Rc<RefCell<RTE<S>>>, values: Vec<Value<S>>) -> Rc<RefCell<Self>>  {
    //let cont = parent.borrow().continuation.clone();
    Rc::new(RefCell::new(Self {
      parent: Some(parent),
      values: values,
//#[cfg(Debug)] n: unsafe { let x=allo; allo=x+1; x}
    }))
  }

  pub fn get(&self, depth: usize, index: usize) -> Option<Value<S>> {
// self.print("get".to_string());
    if depth == 0 {
      return Some(self.values[index].clone());
    }
    else if let Some(parent) = &self.parent {
// println!("Again {}", depth-1);
      return parent.borrow().get(depth - 1, index)
    } else {
      return None
    }
  }

  pub fn set(&mut self, depth: usize, index: usize, value: Value<S>) -> bool {
    if depth==0 {
      self.values[index]=value;
      return true
    }
    else if let Some(parent) = &self.parent {
      return parent.borrow_mut().set(depth-1, index, value)
    } else {
      return false
    }
  }

  pub fn into_ret_values(from: Rc<RefCell<RTE<S>>>) -> Vec<Value<S>> {
    match Rc::try_unwrap(from) {
      Ok(cell) => { cell.into_inner().values }
      Err(from) => { from.borrow().values.to_vec() }
    }
  }

  pub fn print<F>(&self, msg: String, f: F) -> () where F: Fn(&Value<S>) -> String {
   println!("{} rte {:p} {}", msg, self, self.values.len());
   for i in 0 .. self.values.len() {
     println!(" {} {}", i, f(&self.values[i]))
   }
  }

  fn printall0<F>(&self, msg: &String, f: F) -> () where F: Fn(&Value<S>) -> String {
//   println!("{} rte {:p} {} #{}", msg, self, self.values.len(), self.n);
   for i in 0 .. self.values.len() {
     println!(" {} {}", i, f(&self.values[i]))
   }
   if let Some(parent) = &self.parent {
     print!("   parent: {:p}", parent.as_ref());
     parent.borrow().printall0(&"   ".to_string(), f);
   }
  }
  pub fn printall<F>(&self, msg: String, f: F) -> () where F: Fn(&Value<S>) -> String {
     self.printall0(&msg, f);
     println!("--- {}", msg);
  }
  pub fn format(&self) -> String {
   return format!("rte {:p} {}", self, self.values.len())
  }

}

use crate::prelude::{Op, RtOp};

pub struct ContinuationChain<S: Symbol> {
  pub  up: Option<Rc<ContinuationChain<S>>>,
  pub rte: Rc<RefCell<RTE<S>>>,
  pub code: RtOp<S>,
}

impl<S: Symbol> ContinuationChain<S> {
  pub fn new(rte: Rc<RefCell<RTE<S>>>, code: RtOp<S>) -> Option<Rc<Self>> {
    Some(Rc::new({ContinuationChain {
       up: None,
       rte: rte,
       code: code,
    }}))
  }
  pub fn initial(rte: Rc<RefCell<RTE<S>>>) -> Option<Rc<Self>> {
    ContinuationChain::new(rte, Rc::new(Op::ReturnToHost))
  }
  pub fn cons(up: Option<Rc<ContinuationChain<S>>>, rte: Rc<RefCell<RTE<S>>>, code: RtOp<S>) -> Option<Rc<Self>> {
    Some(Rc::new({ContinuationChain {
       up: up,
       rte: rte,
       code: code,
    }}))
  }
}

pub type RtContinuationChain<S> = Option<Rc<ContinuationChain<S>>>;
