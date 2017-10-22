//first some functions to handle permutations
function Permutation(disjointCycles){
  this.disjointCycles = disjointCycles;
}
Permutation.prototype.act = function(x){
  var next = x;
  this.disjointCycles.forEach(function(c){
    var i = c.indexOf(x);
    if(i>=0) next = c[(i+1) % c.length];
  });
  return next;
}
Permutation.prototype.actOn = function(object, list){
  var res = {};
  var me = this;
  list.forEach(function(it){
    res[me.act(it)] = object[it];
  });
  return res;
}
Permutation.prototype.inverse = function(){
  return new Permutation(this.disjointCycles.map(function(x){return x.slice().reverse();}));
}
Permutation.prototype.times = function(g){
  var elts = [];
  var addelt = function(e){if(elts.indexOf(e)<0) elts.push(e);}
  this.disjointCycles.forEach(function(y){y.forEach(addelt);});
  g.disjointCycles.forEach(function(y){y.forEach(addelt);});
  elts.sort();
  var elts2 = new Array(elts.length);
  var cycles = [];
  var i;
  for(i = 0; i < elts.length; i++){ elts2[i] = [elts[i], true];}
  for(i = 0; i < elts.length; i++){
    if(elts2[i][1]){
      var cycle = [];
      var x0,x,i2;
      x0 = x = elts2[i][0]
      i2 = i;
      elts2[i2][1] = false;
      do {
        cycle.push(x);
        x = this.act(g.act(x));
        i2 = elts.indexOf(x);
        elts2[i2][1] = false;
      } while(x != x0)
      cycles.push(cycle);
    }
  }
  return new Permutation(cycles);
}
Permutation.prototype.pow = function(n){
  if(n == 0) return new Permutation([]);
  if(n < 0) return this.inverse.pow(-n);
  var elts = [];
  var addelt = function(e){if(elts.indexOf(e)<0) elts.push(e);}
  this.disjointCycles.forEach(function(y){y.forEach(addelt);});
  elts.sort();
  var elts2 = new Array(elts.length);
  var cycles = [];
  var i;
  for(i = 0; i < elts.length; i++){ elts2[i] = [elts[i], true];}
  for(i = 0; i < elts.length; i++){
    if(elts2[i][1]){
      var cycle = [];
      var x0,x,i2;
      x0 = x = elts2[i][0];
      i2=i;
      elts[i2][1]=false
      do {
        cycle.push(x);
        for(var j = 0; j < n; j++){
          x = this.act(x);
        }
        i2 = elts.indexOf(x);
        elts2[i2][1] = false;
      } while(x!=x0)
      cycles.push(cycle);
    }
  }
  return new Permutation(cycles);
}
Permutation.prototype.toString = function(){
  return ("(" + this.disjointCycles.map(function(x){return x.length>1 ? x.join(" ") : "";}).join(")(") + ")").replace(/\(\)/g, "") || "()";
}

//butterfly puzzle
//have d=1
//√5/2 < r < 5√2/6
//i.e 1.11804 < r < 1.1785
//two circles centred at (-1/2,0) and (1/2,0)
//each has radius r
function verify_r(r){
  return (Math.sqrt(5)/2 < r) && (r < 5*Math.sqrt(2)/6);
}

//sets the transform for c such that
//the rectangle from (-1/2 - r, r) to (1/2+r, r) is included in the screen
//and the aspect ratio is preserved
function initialiseTransform(c,r){
  //c.setTransform(a, b, c, d, e, f) -->
  //[a c e]
  //[b d f]
  //[0 0 1]
  var fudge = 5;
  var w = c.canvas.width - fudge;
  var h = c.canvas.height - fudge;
  var newh = 2*r;
  var neww = 1 + newh;
  var sf = Math.min(h/newh, w/neww);
  var sw = sf*neww;
  var sh = sf*newh;
  //c.setTransform(sf, 0, 0, -sf, 0, 0) will take
  //(-1/2 - r, r) to (-sw/2, -sh/2)
  //want: either (0, abit) or (abit, 0)
  //know: either -sw/2 = -w/2  or -sh/2 = -h/2
  //so:
  c.setTransform(sf, 0, 0, -sf, Math.max(sw/2, w/2) + fudge/2, Math.max(sh/2, h/2) + fudge/2);
  c.lineWidth/=sf;
}

//transforms the canvas such that the circle centred at (cx, cy) of radius r appears as
//the circle centred at (0,0) of radius 1
//optionally rotates anticlockwise by given angle
//returns the separation between cicles scaled to this state
function circleRelative(c, r, cx, cy, rotation){
  c.translate(cx, cy);
  c.scale(r, r)
  c.lineWidth/=r;
  if(rotation){
    c.rotate(rotation);
  }
  return 1/r;
}
//executes fun in a saved state. restores afterwards;
function withSavedState(c, fun){
  c.save();
  try{
    fun();
  } finally {
    c.restore();
  }
}

//assuming that one circle (radius 1) is centred at (0,0) and that the lattice gap is d,
//begin close a path for one of the parts of the puzzle as indexed by n: (groups are X-shaped)
// 0 central piece of the group directly to the right of the centre
// 1 top-left piece of the group directly to the right of the centre
// 2 top-right piece of the group directly to the right of the centre
// 3 bottom-right piece of the group directly to the right of the centre
// 4 bottom-left piece of the group directly to the right of the centre
function pathPart(c,d,n){
  c.beginPath();
  var θ = Math.acos(d/2);  //the angle between x-axis and the intersection of the circle at O with the one directly to the right
  var θ2 = Math.acos(d);
  var α = Math.acos(d*Math.sqrt(5)/2)
  var θ3 = α + Math.atan(2);
  var θ4 = α + Math.atan(1/2);
  var π = Math.PI;
  var π2 = Math.PI/2;
  switch(n){
    case 0: //centre
    c.arc(0,-d,1, θ, π2-θ2,true); //top-right
    c.arc(0, d,1, θ2-π2,-θ,true); //bottom-right
    c.arc(d, d,1,θ-π,-π2-θ2,true); //bottom-left
    c.arc(d,-d,1,π2+θ2,π-θ,true); //top-left
    break;
    case 1: //top-left
    c.arc(0,-d,1, θ, θ3); //upper
    c.arc(d, d,1,-θ4-π2, -π2-θ2); //lower
    c.arc(d,-d,1,π2+θ2,π-θ,true); //top-left (of centre)
    break;
    case 2: //top-right
    c.arc(0, d,1, θ2-π2,θ4-π2); //lower
    c.arc(d,-d,1, π-θ3,π-θ); //upper
    c.arc(0,-d,1, θ, π2-θ2,true); //top-right (of centre)
    break;
    case 3: //bottom-right
    c.arc(d, d,1, θ-π,θ3-π); //lower
    c.arc(0,-d,1,π2-θ4,π2-θ2); //upper
    c.arc(0, d,1, θ2-π2,-θ,true); //bottom-right (of centre)
    break;
    case 4: //bottom-left
    c.arc(d,-d,1, π2+θ2,π2+θ4); //upper
    c.arc(0, d,1, -θ3, -θ); //lower
    c.arc(d, d,1,θ-π,-π2-θ2,true); //bottom-left (of centre)
  }
  c.closePath();
}

//maps name to [centre, rotation, part]
//where centre is an index into centres = [[x,y]...] (coords in lattice)
//rotation is an index into [0, π/2, π, 3π/2]
//part refers to pathPart
//means drawing a part by drawing part at centre then rotating by rotation
//split into:
// leftOnly = only in left circle, centre relative to left circle
// rightOnly = only in right circle, centre relative to right circle
// left = in left and right, centre relative to left circle
// right = in left and right, centre relative to right circle
var placeNames = "a1,a2,a3,a4,a5,b1,b2,b3,b4,b5,c1,c2,c3,c4,c5,d1,d2,d3,d4,d5,e1,e2,e3,e4,e5,f1,f2,f3,f4,f5,g1,g2,g3,g4,g5,h1,h2,h3,h4,h5,i1,i2,i4,i5,j1,j2,j3,j5,k1,k2,k4,k5,l1,l2,l3,l5,m1,m2,m3,m4,m5,n1,n2,n3,n4,o1,o3,o4,o5,p1,p2,p3,p4,q1,q3,q4,q5".split(",");
var places = {
    leftOnly: {
      centres:[[0,0],[0,1],[-1,0],[0,-1]], //middle, top, left, bottom
      a5:[0,1,2],
      c2:[0,3,3],
      d1:[0,2,0],
      d2:[0,2,3],
      d3:[0,2,4],
      d4:[0,2,1],
      d5:[0,2,2],
      h5:[3,0,4],
      i1:[3,2,0],
      i2:[3,2,1],
      i4:[3,2,3],
      i5:[3,2,4],
      j1:[2,3,0],
      j2:[2,3,1],
      j3:[2,3,2],
      j5:[2,3,4],
      k1:[2,1,0],
      k2:[2,1,1],
      k4:[2,1,3],
      k5:[2,1,4],
      l1:[1,2,0],
      l2:[1,2,1],
      l3:[1,2,2],
      l5:[1,2,4],
      m2:[1,0,1]
    },
    rightOnly: {
      centres:[[0,0],[0,1],[1,0],[0,-1]], //middle top right bottom
      e4:[0,1,3],
      f1:[0,0,0],
      f2:[0,0,1],
      f3:[0,0,2],
      f4:[0,0,3],
      f5:[0,0,4],
      g3:[0,3,2],
      h4:[3,2,1],
      m3:[1,2,4],
      n1:[1,0,0],
      n2:[1,0,3],
      n3:[1,0,4],
      n4:[1,0,1],
      o1:[2,1,0],
      o2:[2,1,3],
      o3:[2,1,4],
      o4:[2,1,1],
      o5:[2,1,2],
      p1:[2,3,0],
      p2:[2,3,3],
      p3:[2,3,4],
      p4:[2,3,1],
      q1:[3,0,0],
      q3:[3,0,4],
      q4:[3,0,1],
      q5:[3,0,2]
    },
    left: {
      centres:[[0,0],[0,1],[1,0],[0,-1]], //middle top right bottom
      a1:[0,1,0],
      a2:[0,1,3],
      a3:[0,1,4],
      a4:[0,1,1],
      b1:[0,0,0],
      b2:[0,0,3],
      b3:[0,0,4],
      b4:[0,0,1],
      b5:[0,0,2],
      c1:[0,3,0],
      c3:[0,3,4],
      c4:[0,3,1],
      c5:[0,3,2],
      e1:[2,1,0],
      e2:[2,1,1],
      e3:[2,1,2],
      e5:[2,1,4],
      g1:[2,3,0],
      g2:[2,3,1],
      g4:[2,3,3],
      g5:[2,3,4],
      h1:[3,0,0],
      h2:[3,0,1],
      h3:[3,0,2],
      m1:[1,0,0],
      m4:[1,0,3],
      m5:[1,0,4]
    },
    right: {
      centres:[[-1,0],[-1,1],[0,0],[-1,-1]], //middle top right bottom
      a1:[0,1,0],
      a2:[0,1,3],
      a3:[0,1,4],
      a4:[0,1,1],
      b1:[0,0,0],
      b2:[0,0,3],
      b3:[0,0,4],
      b4:[0,0,1],
      b5:[0,0,2],
      c1:[0,3,0],
      c3:[0,3,4],
      c4:[0,3,1],
      c5:[0,3,2],
      e1:[2,1,0],
      e2:[2,1,1],
      e3:[2,1,2],
      e5:[2,1,4],
      g1:[2,3,0],
      g2:[2,3,1],
      g4:[2,3,3],
      g5:[2,3,4],
      h1:[3,0,0],
      h2:[3,0,1],
      h3:[3,0,2],
      m1:[1,0,0],
      m4:[1,0,3],
      m5:[1,0,4]
    }
}

//rotate left disc clockwise
var σ1 = new Permutation("a1 b1 c1 d1)(a2 b2 c2 d2)(a3 b3 c3 d3)(a4 b4 c4 d4)(a5 b5 c5 d5)(e1 h1 j1 l1)(g1 i1 k1 m1)(e3 h3 j3 l3)(e5 h5 j5 l5)(e2 h2 j2 l2)(g2 i2 k2 m2)(g4 i4 k4 m4)(g5 i5 k5 m5".split(")(").map(function(s){return s.split(" ")}));
var σ2 = new Permutation("b1 e1 f1 g1)(b2 e2 f2 g2)(b3 e3 f3 g3)(b4 e4 f4 g4)(b5 e5 f5 g5)(a1 n1 p1 h1)(a2 n2 p2 h2)(a3 n3 p3 h3)(a4 n4 p4 h4)(c1 m1 o1 q1)(c3 m3 o3 q3)(c4 m4 o4 q4)(c5 m5 o5 q5".split(")(").map(function(s){return s.split(" ")}));

//run fun(name) where each time the context c has a path for the place with that name (given in placeBits. e.g. placeBits = places.leftOnly)
function mapPlacePaths(c, d, placeBits, fun){
  if(placeBits.length){
    return placeBits.forEach(function(x){mapPlacePaths(c,d,x,fun);});
  }
  for(var i = 0; i < placeNames.length; i++){
    var n = placeNames[i];
    var b,p;
    if((b = placeBits[n])){
      try{
        c.save();
        p = placeBits.centres[b[0]];
        circleRelative(c,1,p[0]*d,p[1]*d,[0, Math.PI/2, Math.PI, 3*Math.PI/2][b[1]]);
        pathPart(c,d,b[2]);
        fun(n);
      } finally {
        c.restore();
      }
    }
  }
}

function computePermutation(a){
  return a.map(function(n){
           switch(n){
             case 0:
             return new Permutation([]);
             case 1:
             return σ1;
             case 2:
             return σ2;
             case -1:
             return σ1.inverse();
             case -2:
             return σ2.inverse();
         }}).reduce(function(a,b){return b.times(a);});
}

function shuffleBoard(board){
  var a = [];
  var rp = function(){
    var n = Math.floor(Math.random() * 4);
    switch(n){
      case 0:
      default:
      return -2;
      case 1:
      return -1;
      case 2:
      return 1;
      case 3:
      return 2;
    }
  };
  while(Math.random() > 1/500 && a.length < 2000){
    a.push(rp());
  }
  var p = computePermutation(a);
  return p.actOn(board, placeNames);
}

function renderButtons(c,r,state){
  var b = state.buttons;
  var d = document.getElementById("d");
  d.innerHTML = "";
  b.forEach(function(spec){ //spec = {text: "h1", actions: [1,2,-1,-2], description: "g₁g₂g₁⁻¹g₂⁻¹"}
    var b1 = document.createElement("BUTTON");
    var b2 = document.createElement("BUTTON");
    b1.className = "left";
    b2.className = "right";
    b1.innerHTML = spec.text;
    b2.innerHTML = spec.text + "⁻¹";
    b1.title = spec.description;
    b2.title = "(" + spec.description + ")⁻¹";
    var advanceSoFar = function(sf, name){
      sf = sf || {actions:[], name:""};
      return {actions: sf.actions, name: name + sf.name};
    }
    b1.onclick = function(){
      removeButtons(d);
      var newstate = {game:state.game, past:state.past, rest:spec.actions, buttons: state.buttons, soFar:advanceSoFar(state.soFar, spec.text)};
      requestAnimationFrame(function(t){render(c,r,newstate,t);});
    };
    b2.onclick = function(){
      removeButtons(d);
      var newstate = {game:state.game, past:state.past, rest:spec.actions.map(function(n){return -n;}).reverse(), buttons: state.buttons, soFar:advanceSoFar(state.soFar, spec.text + "⁻¹")};
      requestAnimationFrame(function(t){render(c,r,newstate,t);});
    };
    d.appendChild(b1);
    d.appendChild(b2);
  });

  if(state.soFar && state.soFar.actions && state.soFar.actions.length > 0){
    var save = document.createElement("BUTTON");
    var steps = document.createElement("BUTTON");
    save.className = "left";
    steps.className = "right";
    steps.disabled = true;
    steps.innerHTML = state.soFar.name;
    save.innerHTML = "save";
    steps.title = computePermutation(state.soFar.actions).toString();
    save.onclick = function(){
      var b = state.buttons.slice();
      b.push({text:"h" + (b.length - 1).toString().replace(/[0-9]/g, function(x){return String.fromCharCode(parseInt(x) + "₀".charCodeAt(0))}), actions: state.soFar.actions, description:state.soFar.name});
      requestAnimationFrame(function(t){render(c,r,{game:state.game, past:state.past, buttons:b, soFar:state.soFar}, r);});
    }
    d.appendChild(save);
    d.appendChild(steps);
  }

  var store = document.createElement("BUTTON");
  var recall = document.createElement("BUTTON");
  store.className = "left";
  recall.className = "right";
  store.innerHTML = "store";
  recall.innerHTML = "recall";
  store.onclick = function(){
    requestAnimationFrame(function(t){render(c,r,{game:state.game, past:state, buttons:state.buttons, soFar:state.soFar}, r);});
  };
  if(state.past){
    recall.onclick = function(){
      requestAnimationFrame(function(t){render(c,r,{game:state.past.game, past:state.past.past, buttons:state.buttons, soFar:state.past.soFar}, r);});
    };
  } else {
    recall.disabled = true;
  }
  d.appendChild(store);
  d.appendChild(recall);

  var shuffle = document.createElement("BUTTON");
  var reset = document.createElement("BUTTON");
  shuffle.className = "left";
  reset.className = "right";
  shuffle.innerHTML = "shuffle";
  reset.innerHTML = "reset";
  shuffle.onclick = function(){
    requestAnimationFrame(function(t){render(c,r,{game:shuffleBoard(state.game), past:state, buttons:state.buttons}, r);});
  };
  reset.onclick = function(){
    requestAnimationFrame(function(t){render(c,r,{game:board, past:state, buttons:state.buttons}, r);});
  };
  d.appendChild(shuffle);
  d.appendChild(reset);
}

function removeButtons(d){
  d.innerHTML = "";
}

var letterColours = {
  a:"rgb(1,1,1)",        
  b:"rgb(140,211,80)",   
  c:"rgb(64,64,205)",    
  d:"rgb(209,198,71)",   
  e:"rgb(224,0,176)",    
  f:"rgb(111,212,163)",  
  g:"rgb(210,70,69)",    
  h:"rgb(133,193,211)",  
  i:"rgb(201,128,64)",   
  j:"rgb(77,47,106)",    
  k:"rgb(132,150,66)",   
  l:"rgb(147,125,197)",  
  m:"rgb(48,93,26)",     
  n:"rgb(252,195,219)",  
  o:"rgb(114,89,50)",    
  p:"rgb(200,197,150)",  
  q:"rgb(122,51,65)"
};

function render(c,r,state,t){
  //clear:
  c.canvas.width=c.canvas.width;
  c.fillStyle = "#f0f0ff";
  c.fillRect(0,0,c.canvas.width, c.canvas.height);
  initialiseTransform(c,r);
  //c.arc(x,y,r,θ0,θ1) (drawn anti-clockwise as we reflect in y)
  var fillFun = function(n){
    var letter = state.game[n];
    c.fillStyle = letterColours[letter] || "rgb(0,0,0)";
    c.fill();
    c.stroke();
  }

  //draw some circles, then fill them white
  c.fillStyle="#ffffff";
  c.strokeStyle="#000000";
  withSavedState(c, function(){
    circleRelative(c,r,-0.5,0); //left
    c.beginPath();
    c.arc(0,0,1,0,2*Math.PI);
    c.stroke();
  });
  withSavedState(c, function(){
    circleRelative(c,r,0.5,0); //right
    c.beginPath();
    c.arc(0,0,1,0,2*Math.PI);
    c.stroke();
  });
  withSavedState(c, function(){
    circleRelative(c,r,-0.5,0); //left
    c.beginPath();
    c.arc(0,0,1,0,2*Math.PI);
    c.fill();
  });
  withSavedState(c, function(){
    circleRelative(c,r,0.5,0); //right
    c.beginPath();
    c.arc(0,0,1,0,2*Math.PI);
    c.fill();
  });

  if(state.rotating){
    if(state.rotating.length){
      var newstate = {game:state.game,
                      past:state.past,
                      buttons:state.buttons,
                      rest:state.rest,
                      oldRestLength:state.oldRestLength,
                      soFar:state.soFar,
                      rotating:{
                        start:t,
                        end:t+state.rotating.length,
                        piece: state.rotating.piece, //-1 for left, 1 for right
                        clockwise: state.rotating.clockwise
                      }
                     };
      return render(c,r,newstate,t);
    } else if(state.rotating.end < t){
      var newstate = {game : {}, past:state.past, buttons:state.buttons, rest:state.rest, oldRestLength:state.oldRestLength, soFar:{actions: state.soFar.actions.slice(), name:state.soFar.name}};
      if(state.rotating.piece == -1){
        if(state.rotating.clockwise){
          newstate.game = σ1.actOn(state.game,placeNames);
          newstate.soFar.actions.push(1);
        } else {
          newstate.game = σ1.inverse().actOn(state.game,placeNames);
          newstate.soFar.actions.push(-1);
        }
      } else {
        if(state.rotating.clockwise){
          newstate.game = σ2.actOn(state.game,placeNames);
          newstate.soFar.actions.push(2);
        } else {
          newstate.game = σ2.inverse().actOn(state.game,placeNames);
          newstate.soFar.actions.push(-2);
        }
      }
      return render(c,r,newstate,t);
    } else {
      if(state.rotating.piece == -1){
        withSavedState(c, function(){
          var d = circleRelative(c,r,-0.5,0,(state.rotating.clockwise ? -1 : 1) * (Math.PI/2) * (t-state.rotating.start)/(state.rotating.end-state.rotating.start)); //left
          mapPlacePaths(c, d, [places.left, places.leftOnly],fillFun);
        });
        withSavedState(c, function(){
          var d = circleRelative(c,r,0.5,0); //right
          mapPlacePaths(c,d,places.rightOnly,fillFun);
        });
      } else {
        withSavedState(c, function(){
          var d = circleRelative(c,r,-0.5,0); //left
          mapPlacePaths(c, d, places.leftOnly,fillFun);
        });
        withSavedState(c, function(){
          var d = circleRelative(c,r,0.5,0,(state.rotating.clockwise ? -1 : 1) * (Math.PI/2) * (t-state.rotating.start)/(state.rotating.end-state.rotating.start)); //right
          mapPlacePaths(c,d,[places.right, places.rightOnly],fillFun);
        });
      }
      requestAnimationFrame(function(t){render(c,r,state,t);});
    }
  } else {

    if(state.rest && state.rest.length > 0){
      var first = state.rest[0];
      var orl = state.oldRestLength || state.rest.length;
      var newrest = state.rest.slice(1);
      var clockwise = first > 0;
      var f = Math.abs(first);
      var newstate = {
          game:state.game,
          past:state.past,
          buttons:state.buttons,
          rest:newrest,
          oldRestLength:orl,
          soFar:state.soFar,
          rotating:{
            length:Math.max(50, (orl<4? 750/orl : 3000/orl)),
            piece: (f==1?-1:1),
            clockwise:clockwise
          }
      };
      return render(c,r,newstate,t);
    }

    //we draw the two circles
    withSavedState(c, function(){
      var d = circleRelative(c,r,-0.5,0); //left
      c.beginPath();
      c.arc(0,0,1,0,2*Math.PI);
      c.stroke();
      mapPlacePaths(c, d, places.leftOnly,fillFun);
    });
    withSavedState(c, function(){
      var d = circleRelative(c,r,0.5,0); //right
      c.beginPath();
      c.arc(0,0,1,0,2*Math.PI);
      c.stroke();
      mapPlacePaths(c,d,[places.right, places.rightOnly],fillFun);
    });
    renderButtons(c,r,state);
  }
}

var board = {a1:"a",a2:"a",a3:"a",a4:"a",a5:"a",b1:"b",b2:"b",b3:"b",b4:"b",b5:"b",c1:"c",c2:"c",c3:"c",c4:"c",c5:"c",d1:"d",d2:"d",d3:"d",d4:"d",d5:"d",e1:"e",e2:"e",e3:"e",e4:"e",e5:"e",f1:"f",f2:"f",f3:"f",f4:"f",f5:"f",g1:"g",g2:"g",g3:"g",g4:"g",g5:"g",h1:"h",h2:"h",h3:"h",h4:"h",h5:"h",i1:"i",i2:"i",i4:"i",i5:"i",j1:"j",j2:"j",j3:"j",j5:"j",k1:"k",k2:"k",k4:"k",k5:"k",l1:"l",l2:"l",l3:"l",l5:"l",m1:"m",m2:"m",m3:"m",m4:"m",m5:"m",n1:"n",n2:"n",n3:"n",n4:"n",o1:"o",o3:"o",o4:"o",o5:"o",p1:"p",p2:"p",p3:"p",p4:"p",q1:"q",q3:"q",q4:"q",q5:"q"};

function doButterfly(o){
  var c = document.getElementById("c").getContext("2d");
  var b = board;
  requestAnimationFrame(function(t){render(c,5*Math.sqrt(2)/6,{game:b,buttons:[{text:"g₁", actions:[1], description:"g₁"},{text:"g₂", actions:[2], description:"g₂"}]},t);});
  o.parentNode.removeChild(o);
}