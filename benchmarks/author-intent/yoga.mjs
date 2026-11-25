// Run next to node_modules containing yoga-layout@3.2.1. Emits measured geometry as TSV.
// Use --shorthand to compare Yoga’s setFlex(1) with an explicit zero basis and equal growth.
// Every resize trial also restores the initial size to check retained layout.
import assert from 'node:assert/strict';
import Yoga, { Align, BoxSizing, Direction, Edge, FlexDirection, Gutter, Overflow, Wrap } from 'yoga-layout';

const shorthand = process.argv.includes('--shorthand');

function add(parent, config, direction) {
  const node = Yoga.Node.createWithConfig(config);
  if (direction !== undefined) node.setFlexDirection(direction);
  parent.insertChild(node, parent.getChildCount());
  return node;
}

function flexShare(node) {
  if (shorthand) {
    node.setFlex(1);
    return;
  }
  node.setFlexBasisPercent(0);
  node.setFlexGrow(1);
  node.setFlexShrink(1);
}

function titleRow(root, config, zeroMin) {
  root.setFlexDirection(FlexDirection.Row);
  root.setGap(Gutter.Column, 8);
  const slot = add(root, config, FlexDirection.Row);
  flexShare(slot);
  if (zeroMin) slot.setMinWidth(0);
  const title = add(slot, config);
  title.setWidth(288);
  title.setFlexShrink(0);
  const action = add(root, config);
  action.setWidth(40);
  action.setFlexShrink(0);
  return () => ({
    slot: slot.getComputedWidth(),
    title: title.getComputedWidth(),
    actionX: action.getComputedLeft(),
  });
}

function cards(root, config, boxSizing, innerPadding) {
  root.setFlexDirection(FlexDirection.Row);
  const nodes = [];
  let middleContent;
  for (let i = 0; i < 3; i++) {
    const card = add(root, config, FlexDirection.Row);
    flexShare(card);
    card.setBoxSizing(boxSizing);
    const content = add(card, config, FlexDirection.Row);
    flexShare(content);
    if (i === 1) {
      const padded = innerPadding ? content : card;
      padded.setPadding(Edge.Horizontal, 18);
      middleContent = innerPadding ? add(content, config) : content;
      if (innerPadding) flexShare(middleContent);
    }
    nodes.push(card);
  }
  return () => ({
    outer: nodes.map(node => node.getComputedWidth()),
    middleContent: middleContent.getComputedWidth(),
  });
}

function listPane(root, config, zeroMin) {
  root.setFlexDirection(FlexDirection.Column);
  const heading = add(root, config);
  heading.setHeight(36);
  heading.setFlexShrink(0);
  const pane = add(root, config, FlexDirection.Column);
  flexShare(pane);
  if (zeroMin) pane.setMinHeight(0);
  const list = add(pane, config, FlexDirection.Column);
  flexShare(list);
  list.setOverflow(Overflow.Scroll);
  let last;
  for (let i = 0; i < 8; i++) {
    last = add(list, config);
    last.setHeight(30);
    last.setFlexShrink(0);
  }
  // Yoga publishes the list and row boxes. It delegates scroll offsets to the host.
  return () => ({
    pane: pane.getComputedHeight(),
    list: list.getComputedHeight(),
    lastRowEnd: last.getComputedTop() + last.getComputedHeight(),
  });
}

function wrappedAction(root, config, autoMargin) {
  root.setFlexDirection(FlexDirection.Row);
  root.setFlexWrap(Wrap.Wrap);
  root.setAlignContent(Align.FlexStart);
  root.setGap(Gutter.Column, 6);
  root.setGap(Gutter.Row, 4);
  let action;
  for (const width of [34, 34, 20]) {
    action = add(root, config);
    action.setWidth(width);
    action.setHeight(10);
    action.setFlexShrink(0);
  }
  if (autoMargin) action.setMarginAuto(Edge.Left);
  return () => ({ actionX: action.getComputedLeft(), actionY: action.getComputedTop() });
}

function run(config, defaults, name, build, boxes) {
  const root = Yoga.Node.createWithConfig(config);
  try {
    const read = build(root, config);
    const measure = ([width, height]) => {
      root.calculateLayout(width, height, Direction.LTR);
      return read();
    };
    const initial = measure(boxes[0]);
    for (const box of boxes) {
      console.log([defaults, name, box.join('x'), JSON.stringify(measure(box))].join('\t'));
    }
    assert.deepEqual(measure(boxes[0]), initial, name);
  } finally {
    root.freeRecursive();
  }
}

console.log('use_web_defaults\tcase\tcontainer\tgeometry');
for (const web of [false, true]) {
  const config = Yoga.Config.create();
  config.setUseWebDefaults(web);
  config.setPointScaleFactor(0);
  try {
    for (const reset of [false, true]) {
      const suffix = reset ? 'zero-min' : 'direct';
      run(config, web, 'toolbar-' + suffix, (root, config) => titleRow(root, config, reset), [[224, 32], [144, 32]]);
      run(config, web, 'list-' + suffix, (root, config) => listPane(root, config, reset), [[224, 160], [224, 112]]);
    }
    for (const [label, sizing, inner] of [
      ['border-box', BoxSizing.BorderBox, false],
      ['content-box', BoxSizing.ContentBox, false],
      ['inner-padding', BoxSizing.ContentBox, true],
    ]) {
      run(config, web, 'cards-' + label, (root, config) => cards(root, config, sizing, inner), [[300, 40], [240, 40]]);
    }
    for (const auto of [true, false]) {
      run(config, web, auto ? 'wrap-auto' : 'wrap-no-margin', (root, config) => wrappedAction(root, config, auto), [[106, 100], [99, 100]]);
    }
  } finally {
    config.free();
  }
}
