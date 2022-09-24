function is_reg(ty) {
 return ty.startsWith("Reg");
}

function cell2color(ty) {
 switch (ty) {
  case "Delay": return "#66A";
  case "clk": return "#93b";
  case "CellNot": return "orange";
  case "And": return "green";
  case "Or": return "yellow";
  case "XNor": return "blue";
  default:
   if (ty.startsWith("Dup"))
    return "black";
   else if (ty.startsWith("Rot"))
    return "gray";
   else if (is_reg(ty))
    return "red";
   else
    throw "case missing";
 }
}

function find_other_cell(x) {
 return everything.find(cell => cell[0] != "Dup" && cell[1] == x);
}

window.addEventListener("load", (e) => {
 const canvas = document.getElementById("netlist");
 const ctx = canvas.getContext("2d");

 const scale = 4;

 const inpy = Math.min(...everything.filter(cell => cell[0] != "Rot" && cell[0] != "Dup").map(cell => cell[2]));
 //console.log(inpy);

 // vlines
 for (var i = 0; i < vlines.length; i++) {
  const [[x1, y1], [x2, y2]] = vlines[i];
  ctx.beginPath();
  ctx.moveTo(x1*scale + scale/2, y1*scale);
  ctx.lineTo(x2*scale + scale/2, y2*scale);
  ctx.lineWidth = 1;
  ctx.strokeStyle = "#aaa";
  ctx.stroke();
 }

 // hlines
 for (var i = 0; i < hlines.length; i++) {
  const [[x1, y1], [x2, y2]] = hlines[i];
  ctx.beginPath();
  ctx.moveTo(x1*scale, y1*scale + scale/2);
  ctx.lineTo(x2*scale, y2*scale + scale/2);
  ctx.lineWidth = 1;
  ctx.strokeStyle = "#aaa";
  ctx.stroke();
 }

 /*
 // duplicators
 const dups = everything.filter(cell => cell[0] == "Dup");
 for (var i = 0; i < dups.length; i++) {
  const [dupty, dupx, dupy] = dups[i];
  const [cellty, cellx, celly] = find_other_cell(dupx);

  ctx.beginPath();
  ctx.moveTo(scale*dupx + scale/2, scale*dupy + scale/2);
  ctx.lineTo(scale*cellx + scale/2, scale*celly + scale/2);
  ctx.lineWidth = 1;
  ctx.strokeStyle = "#aaa";
  ctx.stroke();
 }
 */

 // actual cells
 for (var i = 0; i < everything.length; i++) {
  const [ty, x, y] = everything[i];

  if (ty == "CellNot" || ty == "And" || ty == "Or" || ty == "XNor") {
   ctx.beginPath();
   ctx.moveTo(scale*x + scale/2, scale*y + scale/2);
   ctx.lineTo(3000, scale*y + scale/2);
   ctx.lineWidth = 1;
   ctx.strokeStyle = "#aaa";
   ctx.stroke();
  }

  ctx.fillStyle = cell2color(ty);
  const size = is_reg(ty) ? 2*scale : scale;
  ctx.fillRect(scale*x, scale*y, size, size);
 }

});
