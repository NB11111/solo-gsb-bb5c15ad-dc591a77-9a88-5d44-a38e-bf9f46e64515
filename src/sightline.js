/*
 * 观众视线遮挡检查 —— 精确几何引擎
 *
 * 观众点 A=(ax,ay,eye)、舞台目标 B=(bx,by,h)，遮挡物为轴对齐矩形盒
 * [x, x+宽] × [y, y+深] × [0, 高]（全部整数厘米）。
 *
 * 对每条观众－目标线段，精确裁剪其与各矩形在水平面（x-y 平面）投影的相交参数区间：
 * 采用 Liang–Barsky 轴向裁剪，全部比值以 BigInt 分数精确表示，
 * 闭区间语义（边界接触算相交），再沿线段在区间端点（线性函数极值必在端点）
 * 判断视线高度 e + t*(h-e) 是否 ≤ 遮挡物高度 H（等于也算被挡）。
 */

/** 大整数安全的整数判断（入参已经过 Number.isInteger 校验，此处兜底） */
function bi(v) {
  return BigInt(v);
}

/** BigInt 分数：{ num, den }，den > 0 */
function frac(num, den) {
  let n = num;
  let d = den;
  if (d < 0n) {
    n = -n;
    d = -d;
  }
  return { num: n, den: d };
}

function fracLt(a, b) {
  return a.num * b.den < b.num * a.den;
}
function fracLe(a, b) {
  return a.num * b.den <= b.num * a.den;
}
function fracEq(a, b) {
  return a.num * b.den === b.num * a.den;
}
function fracMin(a, b) {
  return fracLt(a, b) ? a : b;
}
function fracMax(a, b) {
  return fracLt(a, b) ? b : a;
}

/** 向负无穷取整（BigInt 分数） */
function fracFloor(a) {
  const q = a.num / a.den; // BigInt 除法向零截断
  const r = a.num % a.den;
  if (a.num < 0n && r !== 0n) return q - 1n;
  return q;
}

/** 输出用：分数转保留 4 位小数的有限数（仅展示，不参与判定） */
function fracToNumber(a) {
  return Number(a.num) / Number(a.den);
}

function round4(x) {
  return Math.round(x * 10000) / 10000;
}

function maxBigInt(arr) {
  return arr.reduce((m, x) => (x > m ? x : m), arr[0]);
}

/**
 * 计算线段 P + t*(Q-P)（0 ≤ t ≤ 1）与闭矩形 [minX,maxX]×[minY,maxY] 的相交参数区间。
 * 全部坐标为整数。返回 { tn, tf }（BigInt 分数，闭区间端点）或 null（不相交）。
 * 边界接触算相交：区间退化为单点（tn=tf）也视为相交。
 */
function clipSegmentRect(ax, ay, bx, by, minX, maxX, minY, maxY) {
  ax = bi(ax); ay = bi(ay); bx = bi(bx); by = bi(by);
  minX = bi(minX); maxX = bi(maxX); minY = bi(minY); maxY = bi(maxY);

  let t0 = frac(0n, 1n);
  let t1 = frac(1n, 1n);

  // 单个轴向 [lo,hi] 的裁剪：更新参数窗口 [t0,t1]
  const cut = (p, q, lo, hi) => {
    // p: 观众端坐标，q: 目标端坐标
    const d = q - p;
    if (d === 0n) {
      // 线段平行于该轴：观众端坐标必须落在闭区间内
      return p >= lo && p <= hi;
    }
    // d·t ∈ [lo-p, hi-p]
    const low = frac(lo - p, d); // d<0 时归一化分母后自动翻转
    const high = frac(hi - p, d);
    t0 = fracMax(t0, fracMin(low, high));
    t1 = fracMin(t1, fracMax(low, high));
    return fracLe(t0, t1);
  };

  if (!cut(ax, bx, minX, maxX)) return null;
  if (!cut(ay, by, minY, maxY)) return null;
  return { tn: t0, tf: t1 };
}

/**
 * 沿线段 A→B 在区间端点 t 处，求解使视线严格越过遮挡物（高 H）的目标高度约束。
 *
 * 视线高度 s(t)=eye+t·(h−eye)，在闭区间上为线性函数，严格越过需 s(t) > H。
 *   t ∈ (0,1)：h > eye + (H−eye)/t → 最小整数 h = floor(eye + (H−eye)/t) + 1
 *   t = 1（目标点在矩形投影内）：h 必须严格大于 H（h = H+1）
 *   t = 0（观众点在矩形投影内）：约束与 h 无关——
 *       eye > H 时端点天然越过、不构成约束（返回 null）；
 *       eye ≤ H 时抬高目标无法抬起观众眼睛，标记 infeasible。
 */
function endpointConstraint(t, eye, height) {
  const e = bi(eye);
  const H = bi(height);
  if (t.num === 0n) {
    return e > H ? { constraint: null } : { infeasible: true };
  }
  if (t.num === t.den) return { constraint: H + 1n };
  // eye + (H-eye)/t
  const valNum = e * t.num + (H - e) * t.den;
  const val = frac(valNum, t.num); // t>0，分母为正
  return { constraint: fracFloor(val) + 1n };
}

/**
 * 分析单对观众－目标相对全部遮挡物的情况。
 *
 * @param {{id,name,x,y,eye}} viewer
 * @param {{id,name,x,y,h}} target
 * @param {Array<{id,name,x,y,width,depth,height}>} blockers
 * @returns 分析结果（含每个相交遮挡物的精确区间、首挡物与建议抬高量）
 */
function analyzeSightline(viewer, target, blockers) {
  const base = {
    viewerId: viewer.id,
    targetId: target.id,
    viewer: { id: viewer.id, name: viewer.name, x: viewer.x, y: viewer.y, eye: viewer.eye },
    target: { id: target.id, name: target.name, x: target.x, y: target.y, h: target.h },
  };
  // 观众点与目标点平面重合：线段退化为点，不做平面裁剪（页面提示移动其中一点）
  if (viewer.x === target.x && viewer.y === target.y) {
    return {
      ...base,
      intersections: [],
      blocked: false,
      firstBlockerId: null,
      firstIntersection: null,
      degenerate: true,
      infeasible: false,
      suggestedHeight: target.h,
      raise: 0,
    };
  }
  const intersections = [];
  for (const o of blockers) {
    const hit = clipSegmentRect(
      viewer.x, viewer.y, target.x, target.y,
      o.x, o.x + o.width, o.y, o.y + o.depth
    );
    if (!hit) continue;

    // 区间端点处视线高度（线性函数极值在端点），判定是否被挡（等于盒高也算）
    const heightAt = (t) =>
      frac(bi(viewer.eye) * t.den + (bi(target.h) - bi(viewer.eye)) * t.num, t.den);
    const H = frac(bi(o.height), 1n);
    const blocked = fracLe(heightAt(hit.tn), H) || fracLe(heightAt(hit.tf), H);

    // 使视线在整个相交区间严格越过该遮挡物所需的最小整数目标高度
    let requiredHeight = null;
    let infeasible = false;
    const constraints = [];
    for (const t of [hit.tn, hit.tf]) {
      const r = endpointConstraint(t, viewer.eye, o.height);
      if (r.infeasible) {
        infeasible = true;
        break;
      }
      if (r.constraint !== null) constraints.push(r.constraint);
    }
    if (!infeasible) requiredHeight = constraints.length ? maxBigInt(constraints) : null;

    // 进入 / 离开点平面坐标（精确分数转展示数），用于绘图与核对
    const pointAt = (t) => ({
      x: round4(fracToNumber(frac(
        bi(viewer.x) * t.den + (bi(target.x) - bi(viewer.x)) * t.num, t.den
      ))),
      y: round4(fracToNumber(frac(
        bi(viewer.y) * t.den + (bi(target.y) - bi(viewer.y)) * t.num, t.den
      ))),
    });
    intersections.push({
      blockerId: o.id,
      blockerName: o.name,
      tn: hit.tn,
      tf: hit.tf,
      tnNumber: round4(fracToNumber(hit.tn)),
      tfNumber: round4(fracToNumber(hit.tf)),
      blocked,
      requiredHeight: requiredHeight === null ? null : Number(requiredHeight.toString()),
      infeasible,
      enterPoint: pointAt(hit.tn),
      exitPoint: pointAt(hit.tf),
    });
  }

  // 排序：按进入参数 tn 升序确定首个遮挡物；tn 相同时取离开参数 tf 较大（覆盖更远）者，
  // 再相同按遮挡物 ID 字典序，保证结果唯一可复现
  intersections.sort((a, b) => {
    if (!fracEq(a.tn, b.tn)) return fracLt(a.tn, b.tn) ? -1 : 1;
    if (!fracEq(a.tf, b.tf)) return fracLt(a.tf, b.tf) ? 1 : -1;
    return a.blockerId < b.blockerId ? -1 : a.blockerId > b.blockerId ? 1 : 0;
  });

  const blocking = intersections.filter((it) => it.blocked);
  const firstBlocker = blocking.length > 0 ? blocking[0] : null;

  // 建议目标高度：使视线严格越过「全部相交遮挡物」的最小整数目标高度
  let suggestedHeight = target.h;
  let infeasibleOverall = false;
  for (const it of intersections) {
    if (it.infeasible) {
      infeasibleOverall = true;
      break;
    }
    if (it.requiredHeight !== null && it.requiredHeight > suggestedHeight) {
      suggestedHeight = it.requiredHeight;
    }
  }

  // 转为可 JSON 序列化结构：BigInt 分数以精确 "p/q" 字符串下发（判定只在服务端完成）
  const items = intersections.map((it) => ({
    blockerId: it.blockerId,
    blockerName: it.blockerName,
    tnExact: `${it.tn.num}/${it.tn.den}`,
    tfExact: `${it.tf.num}/${it.tf.den}`,
    tn: it.tnNumber,
    tf: it.tfNumber,
    blocked: it.blocked,
    requiredHeight: it.requiredHeight,
    infeasible: it.infeasible,
    enterPoint: it.enterPoint,
    exitPoint: it.exitPoint,
  }));
  const firstItem = firstBlocker
    ? items.find((it) => it.blockerId === firstBlocker.blockerId)
    : null;

  return {
    viewerId: viewer.id,
    targetId: target.id,
    viewer: { id: viewer.id, name: viewer.name, x: viewer.x, y: viewer.y, eye: viewer.eye },
    target: { id: target.id, name: target.name, x: target.x, y: target.y, h: target.h },
    intersections: items,
    blocked: blocking.length > 0,
    firstBlockerId: firstBlocker ? firstBlocker.blockerId : null,
    firstIntersection: firstItem || null,
    degenerate: false,
    infeasible: infeasibleOverall,
    suggestedHeight: infeasibleOverall ? null : suggestedHeight,
    raise: infeasibleOverall ? null : Math.max(0, suggestedHeight - target.h),
  };
}

/** 批量分析：全部观众 × 全部目标 */
function analyzeAll(data) {
  const pairs = [];
  for (const v of data.viewers || []) {
    for (const t of data.targets || []) {
      pairs.push(analyzeSightline(v, t, data.blockers || []));
    }
  }
  const blockedPairs = pairs.filter((p) => p.blocked).length;
  const infeasiblePairs = pairs.filter((p) => p.infeasible).length;
  return {
    pairs,
    summary: {
      viewers: (data.viewers || []).length,
      targets: (data.targets || []).length,
      blockers: (data.blockers || []).length,
      pairs: pairs.length,
      blockedPairs,
      clearPairs: pairs.length - blockedPairs,
      infeasiblePairs,
    },
  };
}

module.exports = { analyzeSightline, analyzeAll, clipSegmentRect };
