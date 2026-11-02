const search = document.getElementById('search');
if (search) {
  const items = [...document.querySelectorAll('[data-search]')];
  const update = () => {
    const words = search.value.toLowerCase().trim().split(/\s+/);
    items.forEach(item => { item.hidden = !words.every(word => item.dataset.search.includes(word)); });
    document.getElementById('count').textContent = `${items.filter(item => !item.hidden).length} matching theories and declarations`;
  };
  search.addEventListener('input', update);
  update();
}
