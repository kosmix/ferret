map <F2> :source keymaps.vim<CR>
map <F12> :call <SID>FerretizeCurrent(expand("<cword>"))<CR>

function! <SID>FerretizeCurrent(word)
  normal msHmt
  let bn = bufname('%')
  if a:word =~ '^[a-z_]\+$'
    let replace_str = "frt_".a:word
    echo "Replacing <".a:word."> with <".replace_str.">."
  elseif a:word =~ '^[A-Z_]\+$'
    let replace_str = "FRT_".a:word
    echo "Replacing <".a:word."> with <".replace_str.">."
  elseif a:word =~ '^[A-Za-z]\+$'
    let replace_str = "Ferret".a:word
    echo "Replacing <".a:word."> with <".replace_str.">."
  else
    echo "No idea what to do with this one"
    normal 'tzt`s
    return
  endif
  exec(":bufdo! %s/\\<".a:word."\\>/".replace_str."/gec | update")
  exe ":silent! :b! ".bn
  normal 'tzt`s
endfunction