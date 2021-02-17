import { compareDate } from '@theme/helpers/utils'

export function filterCategoriesByLang (categories, lang) {
  let results = categories.map((category) => {
    category.pages = category.pages.filter((item) => {
      return !(item.frontmatter.lang) || item.frontmatter.lang == lang
    })
    return category
  })
  return results
}

export function filterTagsByLang (tags, lang) {
  let results = tags.map((tag) => {
    tag.pages = tag.pages.filter((item) => {
      return !(item.frontmatter.lang) || item.frontmatter.lang == lang
    })
    return tag
  })
  return results
}


// 过滤博客数据
export function filterPostsByLang (posts, lang) {
  posts = posts.filter((item) => {
    return !(item.frontmatter.lang) || item.frontmatter.lang == lang
  })
  return posts
}

export function filterPosts (posts, isTimeline) {
  posts = posts.filter((item, index) => {
    const { title, frontmatter: { home, date, publish } } = item
    // 过滤多个分类时产生的重复数据
    if (posts.indexOf(item) !== index) {
      return false
    } else {
      const someConditions = home == true || title == undefined || publish === false
      const boo = isTimeline === true
        ? !(someConditions || date === undefined)
        : !someConditions
      return boo
    }
  })
  return posts
}

// 排序博客数据
export function sortPostsByStickyAndDate (posts) {
  posts.sort((prev, next) => {
    const prevSticky = prev.frontmatter.sticky
    const nextSticky = next.frontmatter.sticky
    if (prevSticky && nextSticky) {
      return prevSticky == nextSticky ? compareDate(prev, next) : (prevSticky - nextSticky)
    } else if (prevSticky && !nextSticky) {
      return -1
    } else if (!prevSticky && nextSticky) {
      return 1
    }
    return compareDate(prev, next)
  })
}

export function sortPostsByDate (posts) {
  posts.sort((prev, next) => {
    return compareDate(prev, next)
  })
}
