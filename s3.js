// 自动打牌
if (game) {
	
  var myhai = [];
  var rest = [];
  var dora = [];
  var last_self_deal = false;
  var nowDoraNum = 0;
  var isLiqi = false;
  var left_tile_count = 69;

  var moqie_seat = -1;
  
  var hai2nxtid = function(hname) {
      var tmp = hai2id(hname);
      if (tmp == 8 || tmp == 17 || tmp == 26) return (tmp - 9);
      if (tmp == 30) return 26;
      if (tmp == 33) return 31;
	  return (tmp + 1);
  }

  var hai2id = function(hname) {
	  var base = 0;
	  if (hname[1] == "m") base = 0;
	  else if (hname[1] == "p") base = 9;
	  else if (hname[1] == "s") base = 18;
	  else if (hname[1] == "z") base = 27;
	  var idx = parseInt(hname[0]);
	  if (idx == 0) idx = 5;
	  return base + idx - 1
  }
  
  var maj2id = function(it) {
	  var base = 0;
	  if (it.val.type == 1) base = 0;
	  else if (it.val.type == 0) base = 9;
	  else if (it.val.type == 2) base = 18;
	  else base = 27;
	  var idx = it.val.index;
	  if (idx == 0) idx = 5;
	  return base + idx - 1;
  }

  var doDiscard = function(r) {
	  // Ajax here (process Liqi, Zimo here)
	  last_self_deal = true;
	  
	  if (r.operation && r.operation.operation_list && r.operation.operation_list.length > 0) {
		  
		  
		  var hasLiqi = false;
		  var hasKang = false;
		  var liqi_select = [];
		  
		  // clear operation list
		  {
			  var hasZimo = false;
			  for (var i = 0; i < r.operation.operation_list.length; ++ i) {
				  var op = r.operation.operation_list[i];
				  if (op.type == mjcore.E_PlayOperation.zimo) {
					  hasZimo = true;
					  break;
				  }
			  }
			  if (hasZimo) {
                  /*
				  setTimeout(function() {
					uiscript.UI_LiQiZiMo.Inst.onBtn_Zimo();	// zimo
				  }, 1000);
				  return;
                  */
			  }
			  
			  for (var i = 0; i < r.operation.operation_list.length; ++ i) {
				  var op = r.operation.operation_list[i];
				  if (op.type == mjcore.E_PlayOperation.liqi) {
					  hasLiqi = true;
					  liqi_select = op.combination; 
					  break;
				  }
			  }
			  
			  for (var i = 0; i < r.operation.operation_list.length; ++ i) {
				  var op = r.operation.operation_list[i];
				  if (op.type == mjcore.E_PlayOperation.an_gang) {
					  hasKang = true;
					  break;
				  }
			  }
		  }
		  
		  if (isLiqi) {

		  }
		  else {
              left_tile_count = r.left_tile_count;
			  // ajax here
			  var xhr = new XMLHttpRequest();
			  xhr.open("POST", "http://127.0.0.1:2356/api", true);
			  xhr.setRequestHeader('Content-type', 'application/json');
			  //xhr.onreadystatechange = function () ;
//              console.log(r.tile);
  //            console.log(view.ViewPlayer_Me.Inst.hand.length);
              if(view.ViewPlayer_Me.Inst.hand.length==14){
                  for(var i=0;i<34;++i) dora[i]=0;
                  for(var i=0;i<view.ViewPlayer_Me.Inst.hand.length;++i)
                      if(view.ViewPlayer_Me.Inst.hand[i].isDora)dora[maj2id(view.ViewPlayer_Me.Inst.hand[i])]+=1;
              }
			  xhr.send(JSON.stringify({
				  "hai": myhai,
				  "rest": rest,
				  "left": r.left_tile_count,
                  "dora": dora
			  }));
		  }
		  
	  }
	  else {	// after liqi
	  
		return; // do nothing
	  }
  };
  
  
  
  
  var inject_func = function(t, e) {
    var n = net.ProtobufManager.lookupType("lq." + t.name);
	r = n.decode(t.data);
      console.log(t.name);
	if (t.name == "ActionNewRound") {
	  rest = [];
	  myhai = [];
	  dora = [];
	  for (var i = 0; i < 34; ++ i) {
		  rest.push(4);
		  myhai.push(0);
		  dora.push(0);
	  }
        for (var i = 1; i < 8;++i){
            rest[i] = 0;
        }
	  for (var i = 0; i < r.doras.length; ++ i) {
		  rest[hai2id(r.doras[i])] -= 1;
	  }
	  for (var i = 0; i < r.tiles.length; ++ i) {
		  var tid = hai2id(r.tiles[i]);
		  rest[tid] -= 1;
		  myhai[tid] += 1;
          for (var j = 0; j < r.doras.length; ++ j) {
              if(tid==hai2nxtid(r.doras[j])) dora[tid] += 1;
          }
	  }
	  last_self_deal = false;
	  nowDoraNum = 1;
	  isLiqi = false;
	  if (r.tiles.length == 14) {
		setTimeout(()=>doDiscard(r),500);
	  }
    }
	else if (t.name == "ActionDiscardTile") {
        if(r.moqie){
            moqie_seat = r.seat;
        }
        else{
            moqie_seat = -1;
        }
	  if (last_self_deal) {
		  last_self_deal = false;
		  myhai[ hai2id(r.tile) ] --;
	  }
	  else {
		  var tid = hai2id(r.tile);
		  rest[ tid ] --;
		  if (r.operation) {
			  var hasRong = false;
			  for (var i = 0; i < r.operation.operation_list.length; ++ i) {
				  if (r.operation.operation_list[i].type == mjcore.E_PlayOperation.rong) {
					  hasRong = true;
					  break;
				  }
			  }
			  if (hasRong) {	// Ron !!!
		//		  setTimeout(function() {
		//			uiscript.UI_ChiPengHu.Inst.onBtn_Hu();
		//		  }, 1500);
			  }
			  else {	// no chi pon kang
                  /*
                  myhai[tid] ++;
                  var xhr = new XMLHttpRequest();
			      xhr.open("POST", "http://127.0.0.1:2356/api", true);
 			      xhr.setRequestHeader('Content-type', 'application/json');
                  xhr.send(JSON.stringify({
                      "hai": myhai,
                      "rest": rest,
                      "left": left_tile_count,
                      "dora": dora
                  }));
                  myhai[tid] --;
	//			  setTimeout(function() {
      //                uiscript.UI_ChiPengHu.Inst.onBtn_Cancel();
		//		  }, 100);
                  */
			  }
		  }
	  }
	  
	  if (r.doras && r.doras.length == nowDoraNum + 1) { // new Dora
		  var tid = hai2id(r.doras[r.doras.length - 1]);
		  rest[tid] -= 1;
		  nowDoraNum += 1;
	  }
	}
	else if (t.name == "ActionDealTile") {
        if(moqie_seat >= 0){
            view.DesktopMgr.Inst.players.forEach(player => {
                if(player.seat == moqie_seat){
                    const tile = player.container_qipai.last_pai;
                    try{
                        tile.model.meshRender.sharedMaterial.setColor(caps.Cartoon.COLOR, new Laya.Vector4(0.8, 0.8, 0.8, 1));
                        tile.model.meshRender.sharedMaterial.setColor=function(t,e){if(e.x<1)this._setColor(t,e);else this._setColor(caps.Cartoon.COLOR, new Laya.Vector4(0.8, 0.8, 0.8, 1)); };
                    } catch (error) {
                        console.error(error);
                    }
                }
            })
        }
	  if (r.tile && r.tile != "") { // self
		  var tid = hai2id(r.tile);
		  myhai[tid] += 1;
		  rest[tid] -= 1;
		  setTimeout(()=>doDiscard(r),500);
	  }
	  
	  if (r.doras && r.doras.length == nowDoraNum + 1) { // new Dora
		  var tid = hai2id(r.doras[r.doras.length - 1]);
		  rest[tid] -= 1;
		  nowDoraNum += 1;
	  }
	}
	else if (t.name == "ActionChiPengGang") {
	  var ats = [];
	  if (r.type == 0) { // Chi
	    ats = [ hai2id(r.tiles[0]), hai2id(r.tiles[1]) ];
	  }
	  else if (r.type == 1) { // Pon
		var tmp = hai2id(r.tiles[0]);
		ats = [tmp, tmp];
	  }
	  else { // Kang
		var tmp = hai2id(r.tiles[0]);
		ats = [tmp, tmp, tmp];
	  }
	  for (var i = 0; i < ats.length; ++ i) {
		  rest[ats[i]] -= 1;
	  }
	}
	else if (t.name == "ActionAnGangAddGang") {
	  if (r.type == 3) { // kang
		var tid = hai2id(r.tiles);
		rest[tid] -= 4;
	  }
	  else {
		var tid = hai2id(r.tiles);
		rest[tid] -= 1;
	  }
	}
	else { // not care
	}
	
  };

  requestAnimationFrame(function autoRun () {
    try {
	  var tmp = view.DesktopMgr.prototype.DoMJAction;
	  view.DesktopMgr.prototype.DoMJAction = function(t, e) {
          inject_func(t, e);
		  
		  tmp.apply(this, [t, e]);
	  }
         
	  uiscript.UI_GameEnd.prototype.onEnable = function() {
		  setTimeout(function ASDNqFA_bq2() {
			  if (uiscript.UI_GameEnd.Inst.enable) {
				  if (uiscript.UI_MJReward.Inst.enable) {
					  uiscript.UI_MJReward.Inst.complete.run();
				  }
				  if (uiscript.UI_MJReward_Activity.Inst.enable) {
					  uiscript.UI_MJReward_Activity.Inst.complete.run();
				  }
				  if (uiscript.UI_MJTask_Progress.Inst.enable) {
					  uiscript.UI_MJTask_Progress.Inst.compelte.run();
				  }
				  if (uiscript.UI_RankChange.Inst.enable) {
					  uiscript.UI_RankChange.Inst.complete.run();
				  }
				  uiscript.UI_GameEnd.Inst.onConfirm();
				  setTimeout(ASDNqFA_bq2, 10000);
			  }
		  }, 10000);
	  };/*
	  var tmp2 = uiscript.UI_Lobby.prototype.onEnable;
	  uiscript.UI_Lobby.prototype.onEnable = function() {
		  setTimeout(function() {
			  uiscript.UI_Lobby.Inst.page0.btn_yibanchang.clickHandler.run();
			  setTimeout(function() {
				  //uiscript.UI_Lobby.Inst.page_rank.content0._childs[0]._childs[0]._childs[0]._childs[0].clickHandler.run();	// tong zhi jian
				  uiscript.UI_Lobby.Inst.page_rank.content0._childs[0]._childs[1]._childs[0]._childs[0].clickHandler.run(); // yin zhi jian
				  setTimeout(function() {
					  //uiscript.UI_Lobby.Inst.page_east_north.btns[0]._childs[0].clickHandler.run();	// si ren dong
					  uiscript.UI_Lobby.Inst.page_east_north.btns[1]._childs[0].clickHandler.run();		// si ren nan
				  }, 2500);
			  }, 2500);
		  }, 3000);
		  tmp2.apply(this, []);
	  }*/
	  
	  
    } catch (error) {
      requestAnimationFrame(autoRun)
    }
  })}

