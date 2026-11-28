/* SPDX-FileCopyrightText: 2026 Bforartists Authors
 *
 * SPDX-License-Identifier: GPL-2.0-or-later */

/** \file
 * \ingroup edmesh
 *
 * Quad Bridge: connect two chains of selected edges that have a different number of segments
 * with quad-based topology.
 *
 * bfa - New tool. C++ adaptation of the "Quad Bridge" add-on by abd3d
 * (https://github.com/abd-3d/quad_bridge). Differences with the add-on, besides being native:
 * - Only the new faces are re-oriented, the existing faces are never flipped.
 * - The selection analysis is robust: branched selections, closed loops and a wrong number of
 *   chains are reported to the user (the add-on could loop forever or cancel silently).
 * - The chains are aligned by distance instead of a dot product, so bent chains don't twist.
 * - Faces that already exist are skipped instead of raising an error halfway through.
 * - Works on every object in edit mode, the new faces are selected.
 */

#include <algorithm>

#include "BLI_map.hh"
#include "BLI_math_base.hh"
#include "BLI_math_vector.hh"
#include "BLI_math_vector_types.hh"
#include "BLI_set.hh"
#include "BLI_vector.hh"

#include "BKE_context.hh"
#include "BKE_editmesh.hh"
#include "BKE_layer.hh"
#include "BKE_report.hh"

#include "DNA_mesh_types.h"
#include "DNA_object_types.h"

#include "bmesh.hh"

#include "ED_mesh.hh"
#include "ED_screen.hh"

#include "RNA_access.hh"
#include "RNA_define.hh"

#include "UI_interface.hh"
#include "UI_interface_layout.hh"

#include "mesh_intern.hh" /* own include */

namespace blender {

/* -------------------------------------------------------------------- */
/** \name Types and Options
 * \{ */

using QBChain = Vector<BMVert *>;

/** Kind of bridge, used to know which options are relevant for the user. */
enum eQBTopology {
  QB_TOPO_GENERAL = 0,
  /** One edge bridged to two edges: the "flow" option applies. */
  QB_TOPO_ONE_TO_TWO = 1,
  /** Chains differing by two edges, an even number of edges on the shortest one. */
  QB_TOPO_GAP_EVEN = 2,
  /** Chains differing by two edges, an odd number of edges on the shortest one. */
  QB_TOPO_GAP_ODD = 3,
};

enum eQBFlow {
  QB_FLOW_DIAMOND = 0,
  QB_FLOW_LEFT = 1,
  QB_FLOW_RIGHT = 2,
};

enum eQBLoopMethod {
  QB_LOOP_OUTER = 0,
  QB_LOOP_INNER = 1,
  QB_LOOP_DIAMOND = 2,
};

static const EnumPropertyItem qb_flow_items[] = {
    {QB_FLOW_DIAMOND, "DIAMOND", 0, "Diamond", "Create a diamond in the middle of the bridge"},
    {QB_FLOW_LEFT, "LEFT", 0, "Left Flow", "Edge flow leaning to the left"},
    {QB_FLOW_RIGHT, "RIGHT", 0, "Right Flow", "Edge flow leaning to the right"},
    {0, nullptr, 0, nullptr, nullptr},
};

static const EnumPropertyItem qb_loop_items[] = {
    {QB_LOOP_OUTER, "OUTER", 0, "Outer Loop", "Add an extra loop between the two chains"},
    {QB_LOOP_INNER,
     "INNER",
     0,
     "Inner Loop",
     "Keep the sides straight and resolve the difference in the middle"},
    {QB_LOOP_DIAMOND, "DIAMOND", 0, "Diamond", "Resolve the difference with a single diamond"},
    {0, nullptr, 0, nullptr, nullptr},
};

static const EnumPropertyItem qb_loop_odd_items[] = {
    {QB_LOOP_OUTER, "OUTER", 0, "Outer Loop", "Add an extra loop between the two chains"},
    {QB_LOOP_INNER,
     "INNER",
     0,
     "Inner Loop",
     "Keep the sides straight and resolve the difference in the middle"},
    {0, nullptr, 0, nullptr, nullptr},
};

struct QBOptions {
  int flow;
  int loop;
  int loop_odd;
};

/** \} */

/* -------------------------------------------------------------------- */
/** \name Selection Analysis
 * \{ */

enum eQBSelectionError {
  QB_SEL_OK = 0,
  QB_SEL_NO_EDGES,
  QB_SEL_BRANCHED,
  QB_SEL_CLOSED_LOOP,
  QB_SEL_CHAIN_COUNT,
};

static float3 qb_co(const BMVert *v)
{
  return float3(v->co);
}

/**
 * Find the two chains of selected edges. Each chain is returned as an ordered list of vertices.
 * The shortest chain is returned as \a r_top, the other one as \a r_bot, and \a r_bot is oriented
 * so that it runs in the same direction as \a r_top.
 */
static eQBSelectionError qb_analyze_selection(BMesh *bm,
                                              QBChain &r_top,
                                              QBChain &r_bot,
                                              int &r_chain_count)
{
  /* Index order makes the result independent of the iteration order of the selection. */
  BM_mesh_elem_index_ensure(bm, BM_VERT);

  Map<BMVert *, Vector<BMEdge *, 2>> links;
  BMIter iter;
  BMEdge *e;
  BM_ITER_MESH (e, &iter, bm, BM_EDGES_OF_MESH) {
    if (!BM_elem_flag_test(e, BM_ELEM_SELECT) || BM_elem_flag_test(e, BM_ELEM_HIDDEN)) {
      continue;
    }
    links.lookup_or_add_default(e->v1).append(e);
    links.lookup_or_add_default(e->v2).append(e);
  }
  if (links.is_empty()) {
    return QB_SEL_NO_EDGES;
  }

  Vector<BMVert *> verts;
  for (BMVert *v : links.keys()) {
    verts.append(v);
  }
  std::sort(verts.begin(), verts.end(), [](const BMVert *a, const BMVert *b) {
    return BM_elem_index_get(a) < BM_elem_index_get(b);
  });

  for (BMVert *v : verts) {
    if (links.lookup(v).size() > 2) {
      return QB_SEL_BRANCHED;
    }
  }

  /* Every vertex has at most two selected edges: a component is either a path (two ends) or a
   * closed loop. Walk the paths starting from their end with the lowest index. */
  Set<BMVert *> visited;
  Vector<QBChain> chains;
  for (BMVert *v_start : verts) {
    if (visited.contains(v_start) || links.lookup(v_start).size() != 1) {
      continue;
    }
    QBChain chain;
    BMVert *prev = nullptr;
    BMVert *cur = v_start;
    while (cur) {
      visited.add(cur);
      chain.append(cur);
      BMVert *next = nullptr;
      for (BMEdge *edge : links.lookup(cur)) {
        BMVert *other = BM_edge_other_vert(edge, cur);
        if (other != prev) {
          next = other;
          break;
        }
      }
      prev = cur;
      cur = next;
    }
    chains.append(std::move(chain));
  }

  for (BMVert *v : verts) {
    if (!visited.contains(v)) {
      return QB_SEL_CLOSED_LOOP;
    }
  }

  r_chain_count = int(chains.size());
  if (chains.size() != 2) {
    return QB_SEL_CHAIN_COUNT;
  }

  if (chains[1].size() < chains[0].size()) {
    r_top = std::move(chains[1]);
    r_bot = std::move(chains[0]);
  }
  else {
    r_top = std::move(chains[0]);
    r_bot = std::move(chains[1]);
  }

  /* Align the direction of both chains: pick the pairing of the end points that is the shortest.
   * (The add-on used a dot product of the end to end vectors, which fails for bent chains.) */
  const float3 t0 = qb_co(r_top.first());
  const float3 t1 = qb_co(r_top.last());
  const float3 b0 = qb_co(r_bot.first());
  const float3 b1 = qb_co(r_bot.last());
  const float parallel = math::distance(t0, b0) + math::distance(t1, b1);
  const float crossed = math::distance(t0, b1) + math::distance(t1, b0);
  if (crossed < parallel) {
    std::reverse(r_bot.begin(), r_bot.end());
  }
  return QB_SEL_OK;
}

/** \} */

/* -------------------------------------------------------------------- */
/** \name Chain Helpers
 * \{ */

struct QBChainMetrics {
  Vector<float> lengths;
  float total = 0.0f;
};

static QBChainMetrics qb_chain_metrics(const QBChain &chain)
{
  QBChainMetrics m;
  for (int i = 0; i < int(chain.size()) - 1; i++) {
    const float length = math::distance(qb_co(chain[i]), qb_co(chain[i + 1]));
    m.lengths.append(length);
    m.total += length;
  }
  return m;
}

/** Point of the chain at the normalized distance \a u along it. */
static float3 qb_sample_chain(const QBChain &chain, const float u, const QBChainMetrics &m)
{
  if (m.total == 0.0f) {
    return qb_co(chain[0]);
  }
  const float target = u * m.total;
  const float eps = m.total * 1.0e-5f;
  float current = 0.0f;
  for (const int i : m.lengths.index_range()) {
    const float length = m.lengths[i];
    if (current + length >= target - eps) {
      const float factor = length > 0.0f ? math::clamp((target - current) / length, 0.0f, 1.0f) :
                                           0.0f;
      return math::interpolate(qb_co(chain[i]), qb_co(chain[i + 1]), factor);
    }
    current += length;
  }
  return qb_co(chain.last());
}

/** Normalized distance along the chain of the vertex at \a index. */
static float qb_u_at_index(const int index, const QBChainMetrics &m)
{
  if (m.total == 0.0f) {
    return 0.0f;
  }
  float dist = 0.0f;
  for (int i = 0; i < index && i < int(m.lengths.size()); i++) {
    dist += m.lengths[i];
  }
  return dist / m.total;
}

/** Vertices `start` to `end - 1` of the chain. */
static QBChain qb_slice(const QBChain &chain, const int start, const int end)
{
  QBChain result;
  for (int i = start; i < end; i++) {
    result.append(chain[i]);
  }
  return result;
}

/** \} */

/* -------------------------------------------------------------------- */
/** \name Geometry Builder
 * \{ */

struct QBBuilder {
  BMesh *bm;
  /** Existing face next to the chains, its attributes (material, smooth) are copied. */
  const BMFace *f_example = nullptr;
  const QBChain *top = nullptr;
  const QBChain *bot = nullptr;

  Vector<BMVert *> new_verts;
  Vector<BMFace *> new_faces;
  int skipped_faces = 0;

  static BMVert *nearest(const QBChain &chain, const float3 &co)
  {
    BMVert *best = chain[0];
    float best_dist = math::distance_squared(qb_co(best), co);
    for (BMVert *v : chain) {
      const float dist = math::distance_squared(qb_co(v), co);
      if (dist < best_dist) {
        best = v;
        best_dist = dist;
      }
    }
    return best;
  }

  /** Create a vertex, its custom data is interpolated between the closest chain vertices. */
  BMVert *vert(const float3 &co)
  {
    BMVert *v = BM_vert_create(bm, co, nullptr, BM_CREATE_NOP);
    BMVert *v_top = nearest(*top, co);
    BMVert *v_bot = nearest(*bot, co);
    const float d_top = math::distance(qb_co(v_top), co);
    const float d_bot = math::distance(qb_co(v_bot), co);
    const float fac = (d_top + d_bot) > 0.0f ? d_top / (d_top + d_bot) : 0.5f;
    BM_data_interp_from_verts(bm, v_top, v_bot, v, fac);
    new_verts.append(v);
    return v;
  }

  BMVert *vert_mid(const float3 &a, const float3 &b, const float t = 0.5f)
  {
    return vert(math::interpolate(a, b, t));
  }

  void face(BMVert *v1, BMVert *v2, BMVert *v3, BMVert *v4 = nullptr)
  {
    BMVert *varr[4] = {v1, v2, v3, v4};
    const int len = v4 ? 4 : 3;
    for (int i = 0; i < len; i++) {
      for (int j = i + 1; j < len; j++) {
        if (varr[i] == varr[j]) {
          skipped_faces++;
          return;
        }
      }
    }
    if (BM_face_exists(varr, len)) {
      skipped_faces++;
      return;
    }
    BMFace *f = BM_face_create_verts(bm, varr, len, f_example, BM_CREATE_NOP, true);
    if (f) {
      new_faces.append(f);
    }
  }
};

/** \} */

/* -------------------------------------------------------------------- */
/** \name Bridge Patterns
 *
 * `top` is always the shortest chain. Chains of n edges have n + 1 vertices.
 * \{ */

/** One edge on `top`, two edges on `bot`. */
static void qb_bridge_one_to_two(QBBuilder &b, const QBChain &top, const QBChain &bot, int method)
{
  BMVert *t0 = top[0], *t1 = top[1];
  BMVert *b0 = bot[0], *b1 = bot[1], *b2 = bot[2];

  if (method == QB_FLOW_DIAMOND) {
    BMVert *m1 = b.vert_mid(qb_co(t0), qb_co(b1), 0.55f);
    BMVert *m2 = b.vert_mid(qb_co(t1), qb_co(b1), 0.55f);
    b.face(t0, m1, b1, b0);
    b.face(t1, b2, b1, m2);
    b.face(t0, t1, m2, m1);
    b.face(m1, m2, b1);
  }
  else if (method == QB_FLOW_LEFT) {
    const float3 p_r = (qb_co(t1) + qb_co(b2)) * 0.5f;
    const float3 p_c = (qb_co(t0) + qb_co(b1) + p_r) / 3.0f;
    BMVert *vr = b.vert(p_r);
    BMVert *vc = b.vert(p_c);
    b.face(t0, b0, b1, vc);
    b.face(vc, b1, b2, vr);
    b.face(t0, vc, vr, t1);
  }
  else {
    const float3 p_l = (qb_co(t0) + qb_co(b0)) * 0.5f;
    const float3 p_c = (qb_co(t1) + qb_co(b1) + p_l) / 3.0f;
    BMVert *vl = b.vert(p_l);
    BMVert *vc = b.vert(p_c);
    b.face(t1, vc, b1, b2);
    b.face(vl, b0, b1, vc);
    b.face(t0, vl, vc, t1);
  }
}

/** Chains differing by two edges: add one loop of quads halfway between them. */
static void qb_bridge_gap_outer(QBBuilder &b, const QBChain &top, const QBChain &bot)
{
  const int n_top = int(top.size()) - 1;
  const QBChainMetrics top_m = qb_chain_metrics(top);
  const QBChainMetrics bot_m = qb_chain_metrics(bot);

  Vector<BMVert *> mid;
  for (int i = 0; i <= n_top; i++) {
    const float u_bot = qb_u_at_index(i + 1, bot_m);
    const float3 v_top = qb_sample_chain(top, u_bot, top_m);
    mid.append(b.vert((v_top + qb_co(bot[i + 1])) * 0.5f));
  }
  b.face(top[0], bot[0], bot[1], mid[0]);
  b.face(mid.last(), bot[bot.size() - 2], bot.last(), top.last());
  for (int i = 0; i < n_top; i++) {
    b.face(top[i], mid[i], mid[i + 1], top[i + 1]);
    b.face(mid[i], bot[i + 1], bot[i + 2], mid[i + 1]);
  }
}

/** Gap of two edges, odd number of edges on the shortest chain, inner loop. */
static void qb_bridge_gap_inner_odd(QBBuilder &b,
                                    const QBChain &long_chain,
                                    const QBChain &short_chain)
{
  const int n_long = int(long_chain.size()) - 1;
  const int n_short = int(short_chain.size()) - 1;
  const QBChain &L = long_chain;
  const QBChain &S = short_chain;

  const int l_left = n_long / 2;
  const int l_right = l_left + 1;
  const int s_left = n_short / 2;
  const int s_right = s_left + 1;

  BMVert *v_left = b.vert((qb_co(L[l_left]) + qb_co(S[s_left])) * 0.5f);
  BMVert *v_right = b.vert((qb_co(L[l_right]) + qb_co(S[s_right])) * 0.5f);

  for (int i = 0; i < l_left; i++) {
    if (i == l_left - 1) {
      b.face(L[i], L[i + 1], v_left, S[i]);
    }
    else {
      b.face(L[i], L[i + 1], S[i + 1], S[i]);
    }
  }

  /* `S[idx]` is the vertex of the short chain facing `L[i]`. */
  for (int i = n_long - 1; i >= l_right; i--) {
    if (i == l_right) {
      b.face(L[i], v_right, S[s_right], L[i + 1]);
    }
    else {
      const int idx = i - 2;
      b.face(L[i], S[idx], S[idx + 1], L[i + 1]);
    }
  }

  b.face(L[l_left], L[l_right], v_right, v_left);
  b.face(v_left, v_right, S[s_right], S[s_left]);
}

static void qb_bridge_even_to_n_two(QBBuilder &b,
                                    const QBChain &top,
                                    const QBChain &bot,
                                    int n_bot);

/** Gap of two edges, even number of edges on the shortest chain, inner loop. */
static void qb_bridge_gap_inner_even(
    QBBuilder &b, const QBChain &top, const QBChain &bot, const int n_top, const int n_bot)
{
  const int side = (n_top - 2) / 2;
  for (int i = 0; i < side; i++) {
    b.face(top[i], top[i + 1], bot[i + 1], bot[i]);
  }
  const int ts = n_top - side;
  const int bs = n_bot - side;
  for (int i = 0; i < side; i++) {
    b.face(top[ts + i], top[ts + i + 1], bot[bs + i + 1], bot[bs + i]);
  }
  qb_bridge_even_to_n_two(b, qb_slice(top, side, ts + 1), qb_slice(bot, side, bs + 1), 4);
}

/** Gap of two edges, even number of edges on the shortest chain, diamond. */
static void qb_bridge_gap_diamond(QBBuilder &b,
                                  const QBChain &top,
                                  const QBChain &bot,
                                  const int n_top)
{
  const int mid = n_top / 2;
  for (int i = 0; i < mid; i++) {
    b.face(top[i], top[i + 1], bot[i + 1], bot[i]);
  }
  b.face(top[mid], bot[mid + 2], bot[mid + 1], bot[mid]);
  for (int i = mid; i < n_top; i++) {
    b.face(top[i], top[i + 1], bot[i + 3], bot[i + 2]);
  }
}

/** One edge on `top`, an odd number of edges on `bot`. */
static void qb_bridge_odd_to_n_one(QBBuilder &b,
                                   const QBChain &top,
                                   const QBChain &bot,
                                   const int n_bot)
{
  if (n_bot == 1) {
    b.face(top[0], bot[0], bot[1], top[1]);
    return;
  }
  const int nr = (n_bot - 1) / 2;
  const int steps = nr + 1;
  const float3 t_first = qb_co(top.first());
  const float3 t_last = qb_co(top.last());

  Vector<std::pair<BMVert *, BMVert *>> rows;
  for (int i = 0; i < nr; i++) {
    const float t = float(i + 1) / float(steps);
    const int bi_l = i + 1;
    const int bi_r = n_bot - 1 - i;
    const float3 ta_l = math::interpolate(t_first, t_last, float(bi_l) / float(n_bot));
    const float3 ta_r = math::interpolate(t_first, t_last, float(bi_r) / float(n_bot));
    BMVert *vl = b.vert_mid(ta_l, qb_co(bot[bi_l]), t);
    BMVert *vr = b.vert_mid(ta_r, qb_co(bot[bi_r]), t);
    rows.append({vl, vr});
  }

  b.face(top[0], rows[0].first, rows[0].second, top[1]);
  for (int i = 0; i < int(rows.size()) - 1; i++) {
    b.face(rows[i].first, rows[i + 1].first, rows[i + 1].second, rows[i].second);
  }
  for (int i = 0; i < int(rows.size()); i++) {
    if (i == 0) {
      b.face(top[0], bot[0], bot[1], rows[0].first);
      b.face(rows[0].second, bot[n_bot - 1], bot[n_bot], top[1]);
    }
    else {
      b.face(rows[i - 1].first, bot[i], bot[i + 1], rows[i].first);
      b.face(rows[i].second, bot[n_bot - i - 1], bot[n_bot - i], rows[i - 1].second);
    }
  }
  b.face(rows.last().first, bot[nr], bot[nr + 1], rows.last().second);
}

/** One edge on `top`, an even number (at least 4) of edges on `bot`. */
static void qb_bridge_even_to_n_one(QBBuilder &b,
                                    const QBChain &top,
                                    const QBChain &bot,
                                    const int n_bot)
{
  /* Two edges are handled by #qb_bridge_one_to_two. */
  BLI_assert(n_bot >= 4);
  const int nr = n_bot / 2;
  const float3 t_first = qb_co(top.first());
  const float3 t_last = qb_co(top.last());

  Vector<std::pair<BMVert *, BMVert *>> rows;
  for (int i = 0; i < nr - 1; i++) {
    const float t = float(i + 1) / float(nr);
    const int bi_l = i + 1;
    const int bi_r = n_bot - 1 - i;
    const float3 ta_l = math::interpolate(t_first, t_last, float(bi_l) / float(n_bot));
    const float3 ta_r = math::interpolate(t_first, t_last, float(bi_r) / float(n_bot));
    BMVert *vl = b.vert_mid(ta_l, qb_co(bot[bi_l]), t);
    BMVert *vr = b.vert_mid(ta_r, qb_co(bot[bi_r]), t);
    rows.append({vl, vr});
  }
  b.face(top[0], rows[0].first, rows[0].second, top[1]);
  for (int i = 0; i < int(rows.size()) - 1; i++) {
    b.face(rows[i].first, rows[i + 1].first, rows[i + 1].second, rows[i].second);
  }
  for (int i = 0; i < int(rows.size()); i++) {
    if (i == 0) {
      b.face(top[0], bot[0], bot[1], rows[0].first);
      b.face(rows[0].second, bot[n_bot - 1], bot[n_bot], top[1]);
    }
    else {
      b.face(rows[i - 1].first, bot[i], bot[i + 1], rows[i].first);
      b.face(rows[i].second, bot[n_bot - i - 1], bot[n_bot - i], rows[i - 1].second);
    }
  }
  const int mid = n_bot / 2;
  b.face(rows.last().first, bot[mid - 1], bot[mid]);
  b.face(rows.last().second, bot[mid], bot[mid + 1]);
  b.face(rows.last().first, bot[mid], rows.last().second);
}

/** Two edges on `top`, an even number of edges on `bot`. */
static void qb_bridge_even_to_n_two(QBBuilder &b,
                                    const QBChain &top,
                                    const QBChain &bot,
                                    const int n_bot)
{
  if (n_bot == 2) {
    b.face(top[0], top[1], bot[1], bot[0]);
    b.face(top[1], top[2], bot[2], bot[1]);
    return;
  }

  const int nr = (n_bot - 2) / 2;
  const int mid = n_bot / 2;
  const QBChainMetrics top_m = qb_chain_metrics(top);
  const QBChainMetrics bot_m = qb_chain_metrics(bot);
  const int steps = nr + 1;

  struct Row {
    BMVert *l, *m, *r;
  };
  Vector<Row> rows;
  for (int i = 0; i < nr; i++) {
    const float t = float(i + 1) / float(steps);
    const int bi_l = i + 1;
    const float3 ta_l = qb_sample_chain(top, qb_u_at_index(bi_l, bot_m), top_m);
    BMVert *v0 = b.vert_mid(ta_l, qb_co(bot[bi_l]), t);
    BMVert *v1 = b.vert_mid(qb_co(top[1]), qb_co(bot[mid]), t);
    const int bi_r = n_bot - 1 - i;
    const float3 ta_r = qb_sample_chain(top, qb_u_at_index(bi_r, bot_m), top_m);
    BMVert *v2 = b.vert_mid(ta_r, qb_co(bot[bi_r]), t);
    rows.append({v0, v1, v2});
  }

  b.face(top[0], rows[0].l, rows[0].m, top[1]);
  b.face(top[1], rows[0].m, rows[0].r, top[2]);
  for (int i = 0; i < int(rows.size()) - 1; i++) {
    const Row &cur = rows[i];
    const Row &nxt = rows[i + 1];
    b.face(cur.l, nxt.l, nxt.m, cur.m);
    b.face(cur.m, nxt.m, nxt.r, cur.r);
  }
  const Row &last = rows.last();
  b.face(last.l, bot[mid - 1], bot[mid], last.m);
  b.face(last.m, bot[mid], bot[mid + 1], last.r);

  QBChain l_chain = {top[0]};
  QBChain r_chain = {top[2]};
  for (const Row &row : rows) {
    l_chain.append(row.l);
    r_chain.append(row.r);
  }
  for (int i = 0; i < nr; i++) {
    b.face(l_chain[i], bot[i], bot[i + 1], l_chain[i + 1]);
  }
  for (int i = 0; i < nr; i++) {
    b.face(r_chain[i], r_chain[i + 1], bot[n_bot - 1 - i], bot[n_bot - i]);
  }
}

/**
 * Two edges on `top`, an odd number of edges on `bot`.
 * \a mid_l and \a mid_r are the vertices already created on the sides (or null).
 */
static void qb_bridge_odd_to_n_two(QBBuilder &b,
                                   const QBChain &top,
                                   const QBChain &bot,
                                   const int n_bot,
                                   BMVert *mid_l,
                                   BMVert *mid_r)
{
  auto top_at = [&](const float u) {
    return u <= 0.5f ? math::interpolate(qb_co(top[0]), qb_co(top[1]), u / 0.5f) :
                       math::interpolate(qb_co(top[1]), qb_co(top[2]), (u - 0.5f) / 0.5f);
  };

  const float u_l = 1.0f / float(n_bot);
  const float u_r = float(n_bot - 1) / float(n_bot);
  const int last = int(bot.size()) - 1;
  if (!mid_l) {
    mid_l = b.vert_mid(qb_co(top[0]), qb_co(bot[0]));
  }
  if (!mid_r) {
    mid_r = b.vert_mid(qb_co(top[2]), qb_co(bot[last]));
  }
  BMVert *tri_l = b.vert_mid(top_at(u_l), qb_co(bot[1]));
  BMVert *tri_r = b.vert_mid(top_at(u_r), qb_co(bot[last - 1]));

  b.face(top[0], top[1], tri_l, mid_l);
  b.face(mid_l, tri_l, bot[1], bot[0]);
  b.face(top[1], top[2], mid_r, tri_r);
  b.face(tri_r, mid_r, bot[last], bot[last - 1]);
  b.face(top[1], tri_r, tri_l);
  if (n_bot - 2 == 1) {
    b.face(tri_l, tri_r, bot[2], bot[1]);
  }
  else {
    qb_bridge_odd_to_n_one(b, {tri_l, tri_r}, qb_slice(bot, 1, last), n_bot - 2);
  }
}

/** General case, both chains have at least 3 edges (or equal counts). */
static void qb_bridge_general(
    QBBuilder &b, const QBChain &top, const QBChain &bot, const int n_top, const int n_bot)
{
  if (n_top % 2 == 0 && n_bot % 2 == 1) {
    const int side_len = (n_top - 2) / 2;
    BMVert *mid_l = nullptr;
    BMVert *mid_r = nullptr;

    BMVert *prev_mid = nullptr;
    for (int i = 0; i < side_len; i++) {
      BMVert *m_curr = prev_mid ? prev_mid : b.vert((qb_co(top[i]) + qb_co(bot[i])) * 0.5f);
      BMVert *m_next = b.vert((qb_co(top[i + 1]) + qb_co(bot[i + 1])) * 0.5f);
      b.face(top[i], top[i + 1], m_next, m_curr);
      b.face(m_curr, m_next, bot[i + 1], bot[i]);
      prev_mid = m_next;
      if (i == side_len - 1) {
        mid_l = m_next;
      }
    }

    const int ts = n_top - side_len;
    const int bs = n_bot - side_len;
    prev_mid = nullptr;
    for (int i = 0; i < side_len; i++) {
      const int t_idx = ts + i;
      const int b_idx = bs + i;
      BMVert *m_curr = prev_mid;
      if (!m_curr) {
        m_curr = b.vert((qb_co(top[t_idx]) + qb_co(bot[b_idx])) * 0.5f);
        if (i == 0) {
          mid_r = m_curr;
        }
      }
      BMVert *m_next = b.vert((qb_co(top[t_idx + 1]) + qb_co(bot[b_idx + 1])) * 0.5f);
      b.face(top[t_idx], top[t_idx + 1], m_next, m_curr);
      b.face(m_curr, m_next, bot[b_idx + 1], bot[b_idx]);
      prev_mid = m_next;
    }

    const QBChain c_top = qb_slice(top, side_len, ts + 1);
    const QBChain c_bot = qb_slice(bot, side_len, bs + 1);
    qb_bridge_odd_to_n_two(b, c_top, c_bot, int(c_bot.size()) - 1, mid_l, mid_r);
    return;
  }

  const bool is_top_odd = (n_top % 2 == 1);
  const int side_len = is_top_odd ? (n_top - 1) / 2 : (n_top - 2) / 2;
  for (int i = 0; i < side_len; i++) {
    b.face(top[i], top[i + 1], bot[i + 1], bot[i]);
  }
  const int ts = n_top - side_len;
  const int bs = n_bot - side_len;
  for (int i = 0; i < side_len; i++) {
    b.face(top[ts + i], top[ts + i + 1], bot[bs + i + 1], bot[bs + i]);
  }
  const QBChain c_top = qb_slice(top, side_len, ts + 1);
  const QBChain c_bot = qb_slice(bot, side_len, bs + 1);
  const int cn_bot = int(c_bot.size()) - 1;

  if (is_top_odd) {
    if (cn_bot == 2) {
      /* The flow option only applies to a lone one-to-two bridge, not to its use here. */
      qb_bridge_one_to_two(b, c_top, c_bot, QB_FLOW_DIAMOND);
    }
    else if (cn_bot % 2 == 0) {
      qb_bridge_even_to_n_one(b, c_top, c_bot, cn_bot);
    }
    else {
      qb_bridge_odd_to_n_one(b, c_top, c_bot, cn_bot);
    }
  }
  else {
    qb_bridge_even_to_n_two(b, c_top, c_bot, cn_bot);
  }
}

/** Pick the pattern from the number of edges of each chain. Returns the kind of bridge. */
static eQBTopology qb_bridge_chains(QBBuilder &b,
                                    const QBChain &top,
                                    const QBChain &bot,
                                    const QBOptions &opt)
{
  const int n_top = int(top.size()) - 1;
  const int n_bot = int(bot.size()) - 1;

  if (n_top == 1 && n_bot == 2) {
    qb_bridge_one_to_two(b, top, bot, opt.flow);
    return QB_TOPO_ONE_TO_TWO;
  }

  if (n_bot - n_top == 2 && n_top > 1) {
    if (n_top % 2 == 1) {
      if (opt.loop_odd == QB_LOOP_INNER) {
        qb_bridge_gap_inner_odd(b, bot, top);
      }
      else {
        qb_bridge_gap_outer(b, top, bot);
      }
      return QB_TOPO_GAP_ODD;
    }
    if (opt.loop == QB_LOOP_INNER) {
      qb_bridge_gap_inner_even(b, top, bot, n_top, n_bot);
    }
    else if (opt.loop == QB_LOOP_DIAMOND) {
      qb_bridge_gap_diamond(b, top, bot, n_top);
    }
    else {
      qb_bridge_gap_outer(b, top, bot);
    }
    return QB_TOPO_GAP_EVEN;
  }

  if (n_top == 1 && n_bot == 3) {
    BMVert *v1 = top[0], *v2 = top[1];
    BMVert *v3 = bot[0], *v4 = bot[1], *v5 = bot[2], *v6 = bot[3];
    const float3 w = (qb_co(v5) - qb_co(v4)) * 0.5f;
    const float3 mc = ((qb_co(v4) + qb_co(v5)) * 0.5f + (qb_co(v1) + qb_co(v2)) * 0.5f) * 0.5f;
    BMVert *v7 = b.vert(mc - w);
    BMVert *v8 = b.vert(mc + w);
    b.face(v1, v3, v4, v7);
    b.face(v7, v4, v5, v8);
    b.face(v8, v5, v6, v2);
    b.face(v1, v7, v8, v2);
  }
  else if (n_top == 1) {
    if (n_bot % 2 == 1) {
      qb_bridge_odd_to_n_one(b, top, bot, n_bot);
    }
    else {
      qb_bridge_even_to_n_one(b, top, bot, n_bot);
    }
  }
  else if (n_top == 2) {
    if (n_bot % 2 == 0) {
      qb_bridge_even_to_n_two(b, top, bot, n_bot);
    }
    else {
      qb_bridge_odd_to_n_two(b, top, bot, n_bot, nullptr, nullptr);
    }
  }
  else {
    qb_bridge_general(b, top, bot, n_top, n_bot);
  }
  return QB_TOPO_GENERAL;
}

/** \} */

/* -------------------------------------------------------------------- */
/** \name Post Processing
 * \{ */

/** An existing face next to one of the chains, used as an example for the new faces. */
static const BMFace *qb_find_example_face(const QBChain &top, const QBChain &bot)
{
  for (const QBChain *chain : {&top, &bot}) {
    for (int i = 0; i < int(chain->size()) - 1; i++) {
      const BMEdge *e = BM_edge_exists((*chain)[i], (*chain)[i + 1]);
      if (e && e->l) {
        return e->l->f;
      }
    }
  }
  return nullptr;
}

/**
 * Make the winding of the new faces consistent with each other and with the existing faces
 * next to the chains. Existing faces are never modified.
 */
static void qb_orient_new_faces(BMesh *bm,
                                const Span<BMFace *> new_faces,
                                const QBChain &top,
                                const QBChain &bot)
{
  if (new_faces.is_empty()) {
    return;
  }

  BM_mesh_elem_hflag_disable_all(bm, BM_FACE, BM_ELEM_TAG, false);
  for (BMFace *f : new_faces) {
    BM_elem_flag_enable(f, BM_ELEM_TAG);
  }

  /* Propagate the winding over the new faces. Neighbors are collected before any flip since
   * flipping a face reorders the radial cycles. */
  Set<BMFace *> visited;
  for (BMFace *seed : new_faces) {
    if (visited.contains(seed)) {
      continue;
    }
    visited.add(seed);
    Vector<BMFace *> stack = {seed};
    while (!stack.is_empty()) {
      BMFace *f = stack.pop_last();
      Vector<std::pair<BMFace *, bool>> neighbors;
      BMLoop *l_first = BM_FACE_FIRST_LOOP(f);
      BMLoop *l_iter = l_first;
      do {
        for (BMLoop *l2 = l_iter->radial_next; l2 != l_iter; l2 = l2->radial_next) {
          BMFace *g = l2->f;
          if (BM_elem_flag_test(g, BM_ELEM_TAG) && !visited.contains(g)) {
            neighbors.append({g, l2->v == l_iter->v});
          }
        }
      } while ((l_iter = l_iter->next) != l_first);

      for (const std::pair<BMFace *, bool> &item : neighbors) {
        if (visited.contains(item.first)) {
          continue;
        }
        visited.add(item.first);
        if (item.second) {
          BM_face_normal_flip(bm, item.first);
        }
        stack.append(item.first);
      }
    }
  }

  /* Compare with the existing faces around the chains. */
  int agree = 0;
  int disagree = 0;
  for (const QBChain *chain : {&top, &bot}) {
    for (int i = 0; i < int(chain->size()) - 1; i++) {
      const BMEdge *e = BM_edge_exists((*chain)[i], (*chain)[i + 1]);
      if (!e || !e->l) {
        continue;
      }
      const BMLoop *l_old = nullptr;
      const BMLoop *l_new = nullptr;
      const BMLoop *l_iter = e->l;
      do {
        if (BM_elem_flag_test(l_iter->f, BM_ELEM_TAG)) {
          l_new = l_new ? l_new : l_iter;
        }
        else {
          l_old = l_old ? l_old : l_iter;
        }
      } while ((l_iter = l_iter->radial_next) != e->l);
      if (l_old && l_new) {
        /* Consistent faces traverse a shared edge in opposite directions. */
        if (l_old->v == l_new->v) {
          disagree++;
        }
        else {
          agree++;
        }
      }
    }
  }

  bool flip_all = false;
  if (agree + disagree > 0) {
    flip_all = disagree > agree;
  }
  else {
    /* No face around the chains: orient from the geometry, so the result is reproducible. */
    const float3 top_dir = qb_co(top.last()) - qb_co(top.first());
    const float3 top_mid = (qb_co(top.first()) + qb_co(top.last())) * 0.5f;
    const float3 bot_mid = (qb_co(bot.first()) + qb_co(bot.last())) * 0.5f;
    const float3 wanted = math::cross(top_dir, bot_mid - top_mid);
    flip_all = math::dot(wanted, float3(new_faces[0]->no)) < 0.0f;
  }
  if (flip_all) {
    for (BMFace *f : new_faces) {
      BM_face_normal_flip(bm, f);
    }
  }

  BM_mesh_elem_hflag_disable_all(bm, BM_FACE, BM_ELEM_TAG, false);
}

/** Copy the loop data (UVs, colors...) of the existing faces to the new faces along shared edges.
 */
static void qb_copy_loop_data(BMesh *bm, const Span<BMFace *> new_faces)
{
  /* Only existing faces are sources, the new faces have no valid loop data yet. */
  for (BMFace *f : new_faces) {
    BM_elem_flag_enable(f, BM_ELEM_TAG);
  }
  for (BMFace *f : new_faces) {
    BM_face_copy_shared(
        bm,
        f,
        [](const BMLoop *l, void * /*user_data*/) {
          return !BM_elem_flag_test(l->f, BM_ELEM_TAG);
        },
        nullptr);
  }
  for (BMFace *f : new_faces) {
    BM_elem_flag_disable(f, BM_ELEM_TAG);
  }
}

/** \} */

/* -------------------------------------------------------------------- */
/** \name Operator
 * \{ */

static wmOperatorStatus edbm_quad_bridge_exec(bContext *C, wmOperator *op)
{
  const Main *bmain = CTX_data_main(C);
  const Scene *scene = CTX_data_scene(C);
  ViewLayer *view_layer = CTX_data_view_layer(C);
  const Vector<Object *> objects = BKE_view_layer_array_from_objects_in_edit_mode_unique_data(
      *bmain, scene, view_layer, CTX_wm_view3d(C));

  QBOptions opt;
  opt.flow = RNA_enum_get(op->ptr, "flow_method");
  opt.loop = RNA_enum_get(op->ptr, "loop_method");
  opt.loop_odd = RNA_enum_get(op->ptr, "loop_method_simple");

  bool changed_multi = false;
  bool skipped_faces = false;
  eQBSelectionError first_error = QB_SEL_OK;
  int error_chain_count = 0;

  for (Object *obedit : objects) {
    BMesh *bm = BKE_editmesh_bmesh_ensure(obedit);
    if (bm->totedgesel == 0) {
      continue;
    }

    QBChain top, bot;
    int chain_count = 0;
    const eQBSelectionError error = qb_analyze_selection(bm, top, bot, chain_count);
    if (error != QB_SEL_OK) {
      if (first_error == QB_SEL_OK) {
        first_error = error;
        error_chain_count = chain_count;
      }
      continue;
    }

    QBBuilder builder;
    builder.bm = bm;
    builder.top = &top;
    builder.bot = &bot;
    builder.f_example = qb_find_example_face(top, bot);

    const eQBTopology topology = qb_bridge_chains(builder, top, bot, opt);

    /* Vertices created for faces that were skipped would stay loose. */
    for (BMVert *v : builder.new_verts) {
      if (v->e == nullptr) {
        BM_vert_kill(bm, v);
      }
    }
    if (builder.skipped_faces > 0) {
      skipped_faces = true;
    }
    if (builder.new_faces.is_empty()) {
      continue;
    }

    /* Tell the redo panel which options are relevant. */
    RNA_int_set(op->ptr, "topology", int(topology));

    qb_orient_new_faces(bm, builder.new_faces, top, bot);
    qb_copy_loop_data(bm, builder.new_faces);

    EDBM_flag_disable_all(bm, BM_ELEM_SELECT);
    for (BMFace *f : builder.new_faces) {
      BM_face_select_set(bm, f, true);
    }

    changed_multi = true;
    EDBMUpdate_Params params{};
    params.calc_looptris = true;
    params.calc_normals = true;
    params.is_destructive = true;
    EDBM_update(id_cast<Mesh *>(obedit->data), &params);
  }

  if (!changed_multi) {
    if (skipped_faces) {
      BKE_report(op->reports, RPT_WARNING, "The faces between the chains already exist");
      return OPERATOR_CANCELLED;
    }
    switch (first_error) {
      case QB_SEL_BRANCHED:
        BKE_report(op->reports,
                   RPT_WARNING,
                   "Selected edges must form two simple chains (a vertex is shared by more than "
                   "two selected edges)");
        break;
      case QB_SEL_CLOSED_LOOP:
        BKE_report(op->reports,
                   RPT_WARNING,
                   "Closed edge loops are not supported, use Bridge Edge Loops instead");
        break;
      case QB_SEL_CHAIN_COUNT:
        BKE_reportf(op->reports,
                    RPT_WARNING,
                    "Select exactly two separate chains of connected edges (found %d)",
                    error_chain_count);
        break;
      case QB_SEL_NO_EDGES:
      case QB_SEL_OK:
        BKE_report(op->reports, RPT_WARNING, "No edges selected");
        break;
    }
    return OPERATOR_CANCELLED;
  }

  if (skipped_faces) {
    BKE_report(op->reports, RPT_INFO, "Some faces already existed and were skipped");
  }
  return OPERATOR_FINISHED;
}

static void edbm_quad_bridge_ui(bContext * /*C*/, wmOperator *op)
{
  ui::Layout &layout = *op->layout;
  layout.use_property_split_set(true);

  switch (RNA_int_get(op->ptr, "topology")) {
    case QB_TOPO_ONE_TO_TWO:
      layout.prop(op->ptr, "flow_method", ui::ITEM_R_EXPAND, std::nullopt, ICON_NONE);
      break;
    case QB_TOPO_GAP_EVEN:
      layout.prop(op->ptr, "loop_method", ui::ITEM_R_EXPAND, std::nullopt, ICON_NONE);
      break;
    case QB_TOPO_GAP_ODD:
      layout.prop(op->ptr, "loop_method_simple", ui::ITEM_R_EXPAND, std::nullopt, ICON_NONE);
      break;
    default:
      break;
  }
}

void MESH_OT_quad_bridge(wmOperatorType *ot)
{
  /* identifiers */
  ot->name = "Quad Bridge";
  ot->description =
      "Connect two chains of selected edges with a different number of segments using quads";
  ot->idname = "MESH_OT_quad_bridge";

  /* API callbacks */
  ot->exec = edbm_quad_bridge_exec;
  ot->poll = ED_operator_editmesh;
  ot->ui = edbm_quad_bridge_ui;

  /* flags */
  ot->flag = OPTYPE_REGISTER | OPTYPE_UNDO;

  /* properties */
  RNA_def_enum(ot->srna,
               "flow_method",
               qb_flow_items,
               QB_FLOW_DIAMOND,
               "Flow",
               "Edge flow used when bridging one edge to two edges");
  RNA_def_enum(ot->srna,
               "loop_method",
               qb_loop_items,
               QB_LOOP_OUTER,
               "Gap Method",
               "How the difference of two edges between the chains is resolved");
  RNA_def_enum(ot->srna,
               "loop_method_simple",
               qb_loop_odd_items,
               QB_LOOP_OUTER,
               "Gap Method",
               "How the difference of two edges between the chains is resolved");

  /* Hidden: result of the last analysis, used to show only the relevant options. */
  PropertyRNA *prop = RNA_def_int(ot->srna, "topology", 0, 0, 3, "Topology", "", 0, 3);
  RNA_def_property_flag(prop, PROP_HIDDEN | PROP_SKIP_SAVE);
}

/** \} */

}  // namespace blender
