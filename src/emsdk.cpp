#include <SDL2/SDL.h>
#include <SDL2/SDL_pixels.h>
#include <csignal>
#include <cstdlib>
#include <ctime>
#include <iostream>
#include <vector>

#ifdef __EMSCRIPTEN__
#include <emscripten.h>
#endif

using namespace std;

vector<SDL_Point> get_random_points() {
  srand(time(NULL));
  vector<SDL_Point> result;
  int curr_y = 400;
  for (int i = 0; i < 100; i++) {
    SDL_Point point;
    point.x = 10 * i + 10;
    auto rand = std::rand();

    if (rand % 2 == 0)
      curr_y += 20;
    else
      curr_y -= 20;

    point.y = curr_y;
    result.push_back(point);
  }

  return result;
}

void draw_stage(SDL_Renderer *ren) {
  SDL_SetRenderDrawColor(ren, 0, 0, 0, SDL_ALPHA_OPAQUE);
  SDL_Rect scene;
  scene.h = 50;
  scene.w = 800;

  scene.x = 50;
  scene.y = 50;

  SDL_RenderDrawRect(ren, &scene);
}

void draw_singer(SDL_Renderer *ren) {
  SDL_SetRenderDrawColor(ren, 0, 0, 0, SDL_ALPHA_OPAQUE);

  SDL_Rect singer;
  singer.h = 10;
  singer.w = 10;
  singer.x = 425;
  singer.y = 75;

  SDL_RenderDrawRect(ren, &singer);
}

void draw_scene(SDL_Renderer *ren) {
  SDL_SetRenderDrawColor(ren, 255, 255, 255, SDL_ALPHA_OPAQUE);
  SDL_RenderClear(ren);

  draw_stage(ren);
  draw_singer(ren);

  SDL_RenderPresent(ren);
  SDL_Delay(4000);
}

extern "C" int main() {
  if (SDL_Init(SDL_INIT_VIDEO) != 0) {
    std::cout << "SDL_Init Error: " << SDL_GetError() << std::endl;
    return 1;
  }

  SDL_Window *win =
      SDL_CreateWindow("Hello World!", 100, 100, 1500, 800, SDL_WINDOW_SHOWN);
  if (win == nullptr) {
    std::cout << "SDL_CreateWindow Error: " << SDL_GetError() << std::endl;
    SDL_Quit();
    return 1;
  }

  SDL_Renderer *ren = SDL_CreateRenderer(
      win, -1, SDL_RENDERER_ACCELERATED | SDL_RENDERER_PRESENTVSYNC);
  if (ren == nullptr) {
    SDL_DestroyWindow(win);
    std::cout << "SDL_CreateRenderer Error: " << SDL_GetError() << std::endl;
    SDL_Quit();
    return 1;
  }

  draw_scene(ren);

  SDL_DestroyRenderer(ren);
  SDL_DestroyWindow(win);
  SDL_Quit();

  return 0;
}

