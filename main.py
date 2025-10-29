# ============================================================
#  Snake Shooter Roguelike
#  Author: alma hadid (middle dev)
#  Version: 1.0.0
#  Date: 2025-10-29
#
#  Description:
#    Experimental hybrid of classic Snake and shooter mechanics.
#    The snake moves smoothly on a cell grid, shoots projectiles
#    toward the mouse, and fights A*-driven enemies that navigate
#    around its tail.
#
#  Features:
#    - Smooth movement and interpolated tail fading
#    - Bullets with hit detection and fade-out effect
#    - Enemies of 3 types with distinct HP/speed/colors
#    - Pathfinding via A* (avoiding tail as obstacles)
#    - Real-time HUD (FPS, coordinates, score, speed)
#
#  License:
#    MIT License
#    Copyright (c) 2025 alma hadid
#
#    Permission is hereby granted, free of charge, to any person obtaining
#    a copy of this software and associated documentation files (the
#    "Software"), to deal in the Software without restriction, including
#    without limitation the rights to use, copy, modify, merge, publish,
#    distribute, sublicense, and/or sell copies of the Software, and to
#    permit persons to whom the Software is furnished to do so, subject to
#    the following conditions:
#
#    The above copyright notice and this permission notice shall be included
#    in all copies or substantial portions of the Software.
#
#    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
#    EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
#    MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
# ============================================================
# ------------------------------------------------------------
#  How to Install, Configure and Start
# ------------------------------------------------------------
#
#  1. Installation
#     Make sure you have Python 3.10 or newer.
#     Install dependencies using pip:
#
#         pip install -r requirements.txt
#
#  2. Configuration
#     Default parameters are defined at the top of the file:
#        RES           – размер окна (пиксели)
#        SIZE          – размер клетки (пиксели)
#        SPEED_CELLS   – скорость змейки (клеток/сек)
#        INIT_LEN      – начальная длина змейки
#     You can adjust these values directly in the script
#     before launching the game.
#
#  3. Start
#     Run the game from the terminal:
#
#         python snake_shooter.py
#
#     To stop the game, close the window or press Ctrl+C
#     in the terminal.
#
# ------------------------------------------------------------
#  Usage:
#
#    python snake_shooter.py
#
#  Controls:
#    W / A / S / D     – движение по клеткам
#    Right Mouse       – выстрел в сторону курсора
#
#  Mechanics:
#    Yellow apple      – увеличивает длину и счёт
#    Enemies           – идут к змейке по A*, обходят хвост
#    Bullets           – не привязаны к сетке, исчезают при попадании
#    Tail              – препятствие для врагов
#
#  UI:
#    В левом верхнем углу отображаются:
#       • FPS
#       • x, y координаты головы
#       • Score (яблоки)
#       • Скорость (клеток/сек)
#
#  Tip:
#    Убей врагов до того, как они доберутся до головы.
#    Не допускай пересечения собственного хвоста.
# ------------------------------------------------------------
# ============================================================

import pygame
from random import randrange, choice, random
from collections import deque
import math, heapq, time

# === Параметры ===
RES = 800
SIZE = 20                  # размер клетки (px)
CELLS = RES // SIZE
SPEED_CELLS = 15           # клеток/с (скорость змейки)
SPEED = SPEED_CELLS * SIZE # пикс/с
INIT_LEN = 5               # стартовая длина змейки в клетках

BULLET_SPEED = 700         # px/s
BULLET_RADIUS = 5
BULLET_FADE_TIME = 0.25    # сек после попадания
ENEMY_SPAWN_EVERY = 1.5    # сек между спавнами
ENEMY_REPATH_EVERY = 0.25  # сек между пересчетом пути A*

pygame.init()
sc = pygame.display.set_mode((RES, RES))
clock = pygame.time.Clock()

# === Состояние змейки на сетке ===
grid_x, grid_y = CELLS//2, CELLS//2
dir_x, dir_y = 1, 0
queued_dir = (1, 0)
progress = 0.0

# === Позиции в пикселях для плавной анимации ===
x = grid_x * SIZE
y = grid_y * SIZE

length_cells = INIT_LEN
path = deque()
path.append((x, y))

game_over = False
body = deque()
body.append((grid_x, grid_y))

# Яблоко — координаты в клетках
apple = (randrange(CELLS), randrange(CELLS))

# HUD / score
score = 0
font_small = pygame.font.SysFont("consolas", 18)
font_big = pygame.font.SysFont("arial", 60, True)

# Пули
bullets = []  # dict: {pos:[x,y], vel:[vx,vy], r, hit, t_hit, alpha}

# Враги (A*)
class Enemy:
    # типы: (имя, hp, speed_cells, color)
    TYPES = [
        ("pink",   1, 15, (255,105,180)),  # 1хп, 15 кл/с
        ("red",    3,  5, (220,0,0)),      # 3хп, 5 кл/с
        ("maroon",15,  2, (128,0,32)),     # 15хп, 2 кл/с
    ]
    def __init__(self, kind, cell):
        name, hp, spd_c, color = Enemy.TYPES[kind]
        self.name = name
        self.hp = hp
        self.speed_px = spd_c * SIZE
        self.color = color
        self.cell = cell[:]  # [cx, cy]
        self.pos = [cell[0]*SIZE + SIZE/2, cell[1]*SIZE + SIZE/2]  # пикс центр
        self.path = []       # список клеток [(cx,cy), ...]
        self.next_idx = 0
        self._repath_timer = 0.0
        self.size = SIZE - 2

    def rect(self):
        return pygame.Rect(int(self.pos[0]-self.size/2), int(self.pos[1]-self.size/2),
                           self.size, self.size)

    def update(self, dt, target_cell, blocked_cells):
        # периодически пересчитываем A*
        self._repath_timer -= dt
        if self._repath_timer <= 0.0 or not self.path:
            self.path = astar(self.cell, target_cell, blocked_cells)
            # path включает стартовую; следующий шаг — 1й элемент после текущего
            self.next_idx = 1 if len(self.path) > 1 else 0
            self._repath_timer = ENEMY_REPATH_EVERY

        # идём к следующему узлу
        if self.next_idx < len(self.path):
            nxt = self.path[self.next_idx]
            target_px = (nxt[0]*SIZE + SIZE/2, nxt[1]*SIZE + SIZE/2)
            dx = target_px[0] - self.pos[0]
            dy = target_px[1] - self.pos[1]
            dist = math.hypot(dx, dy)
            if dist > 1e-6:
                step = self.speed_px * dt
                if step >= dist:
                    # достигли клетки
                    self.pos[0], self.pos[1] = target_px
                    self.cell = [nxt[0], nxt[1]]
                    self.next_idx += 1
                else:
                    self.pos[0] += dx/dist * step
                    self.pos[1] += dy/dist * step

# список врагов
enemies = []
last_spawn_time = 0.0

def move_to_cell(xc, yc, dx, dy):
    nx, ny = xc + dx, yc + dy
    if nx < 0 or nx >= CELLS or ny < 0 or ny >= CELLS:
        return None
    return nx, ny

def can_turn(current, new):
    return not (current[0] == -new[0] and current[1] == -new[1])

def trim_path_to_length(path_deque, max_len_px):
    if len(path_deque) <= 1:
        return
    pts = list(path_deque)
    dists = []
    for i in range(len(pts) - 1, 0, -1):
        x2, y2 = pts[i]
        x1, y1 = pts[i - 1]
        dists.append(math.hypot(x2 - x1, y2 - y1))
    total = 0.0
    keep_from = len(pts) - 1
    for idx, d in enumerate(dists, start=1):
        if total + d >= max_len_px:
            keep_from = len(pts) - 1 - idx
            leftover = max_len_px - total
            x0, y0 = pts[keep_from]
            x1, y1 = pts[keep_from + 1]
            seg_len = math.hypot(x1 - x0, y1 - y0) or 1.0
            t = leftover / seg_len
            new_tail = (x1 + (x0 - x1) * (1 - t), y1 + (y0 - y1) * (1 - t))
            new_path = deque()
            new_path.append(new_tail)
            for j in range(keep_from + 1, len(pts)):
                new_path.append(pts[j])
            path_deque.clear()
            path_deque.extend(new_path)
            return
        total += d

def draw_fading_path(surface, path_deque, color=(0, 255, 0), fade_to=0, width=None):
    if len(path_deque) < 2: return
    N = len(path_deque) - 1
    tail_surf = pygame.Surface((RES, RES), pygame.SRCALPHA)
    if width is None:
        width = SIZE - 6
    width = max(2, width)
    for i in range(N):
        x1, y1 = path_deque[i]
        x2, y2 = path_deque[i + 1]
        alpha = int(fade_to + (255 - fade_to) * (i + 1) / (N + 1))
        col = (color[0], color[1], color[2], alpha)
        pygame.draw.line(tail_surf, col, (x + SIZE/2 for x in (x1, y1)))
        pygame.draw.line(tail_surf, col, (x1 + SIZE/2, y1 + SIZE/2),
                         (x2 + SIZE/2, y2 + SIZE/2), width)
    surface.blit(tail_surf, (0, 0))

def draw_fading_path(surface, path_deque, color=(0, 220, 80), fade_to=10, width=None):
    if len(path_deque) < 2: return
    N = len(path_deque) - 1
    tail_surf = pygame.Surface((RES, RES), pygame.SRCALPHA)
    if width is None:
        width = SIZE - 6
    width = max(2, width)
    for i in range(N):
        x1, y1 = path_deque[i]
        x2, y2 = path_deque[i + 1]
        alpha = int(fade_to + (255 - fade_to) * (i + 1) / (N + 1))
        col = (color[0], color[1], color[2], alpha)
        pygame.draw.line(tail_surf, col, (x1 + SIZE/2, y1 + SIZE/2),
                         (x2 + SIZE/2, y2 + SIZE/2), width)
    surface.blit(tail_surf, (0, 0))

def head_rect():
    return pygame.Rect(int(x + 2), int(y + 2), SIZE - 4, SIZE - 4)

def spawn_enemy():
    # спавним на границе (имитация «из-за экрана»)
    side = choice(["top","bottom","left","right"])
    if side in ("top","bottom"):
        cx = randrange(CELLS)
        cy = 0 if side=="top" else CELLS-1
    else:
        cy = randrange(CELLS)
        cx = 0 if side=="left" else CELLS-1
    kind = choice([0,0,0,1,1,2])  # веса: больше розовых/красных, редко бордовые
    return Enemy(kind, [cx, cy])

def astar(start, goal, blocked):
    # A* на 4-соседях
    sx, sy = start
    gx, gy = goal
    if not (0 <= sx < CELLS and 0 <= sy < CELLS): return []
    if not (0 <= gx < CELLS and 0 <= gy < CELLS): return []
    blocked_set = set(blocked)
    def h(x, y): return abs(x - gx) + abs(y - gy)
    openh = []
    heapq.heappush(openh, (h(sx,sy), 0, (sx,sy)))
    came = {}
    g = { (sx,sy): 0 }
    visited = set()
    while openh:
        _, gc, (cx, cy) = heapq.heappop(openh)
        if (cx, cy) in visited: continue
        visited.add((cx, cy))
        if (cx, cy) == (gx, gy):
            # восстановление пути
            path = [(cx, cy)]
            while (cx, cy) in came:
                cx, cy = came[(cx, cy)]
                path.append((cx, cy))
            path.reverse()
            return path
        for dx, dy in ((1,0),(-1,0),(0,1),(0,-1)):
            nx, ny = cx+dx, cy+dy
            if not (0 <= nx < CELLS and 0 <= ny < CELLS): continue
            if (nx, ny) in blocked_set and (nx, ny) != (gx, gy):
                continue
            ng = gc + 1
            if ng < g.get((nx,ny), 1e9):
                g[(nx,ny)] = ng
                came[(nx,ny)] = (cx, cy)
                heapq.heappush(openh, (ng + h(nx,ny), ng, (nx,ny)))
    return [(sx,sy)]  # без пути – стоим

##########################################################
#
#                 MAIN CYCLE
#
##########################################################
t0 = time.time()
while True:
    dt = clock.tick(60) / 1000.0
    now = time.time()

    # === События ===
    for event in pygame.event.get():
        if event.type == pygame.QUIT:
            pygame.quit(); raise SystemExit
        elif event.type == pygame.KEYDOWN:
            ndx, ndy = dir_x, dir_y
            if event.key in (pygame.K_w, pygame.K_UP):    ndx, ndy = 0, -1
            elif event.key in (pygame.K_s, pygame.K_DOWN): ndx, ndy = 0,  1
            elif event.key in (pygame.K_a, pygame.K_LEFT): ndx, ndy = -1, 0
            elif event.key in (pygame.K_d, pygame.K_RIGHT):ndx, ndy = 1,  0
            if (ndx, ndy) != (dir_x, dir_y) and can_turn((dir_x, dir_y), (ndx, ndy)):
                queued_dir = (ndx, ndy)
        elif event.type == pygame.MOUSEBUTTONDOWN and event.button == 3:
            # выстрел из головы в сторону мыши
            mx, my = pygame.mouse.get_pos()
            hx, hy = x + SIZE/2, y + SIZE/2
            vx, vy = mx - hx, my - hy
            d = math.hypot(vx, vy) or 1.0
            vx, vy = vx/d * BULLET_SPEED, vy/d * BULLET_SPEED
            bullets.append({
                "pos":[hx,hy],
                "vel":[vx,vy],
                "r": BULLET_RADIUS,
                "hit": False,
                "t_hit": 0.0,
                "alpha": 255
            })

    # === Движение змейки — строго по клеткам, с плавной интерполяцией ===
    move_px = SPEED * dt
    progress += move_px / SIZE

    while progress >= 1.0 and not game_over:
        progress -= 1.0
        if queued_dir != (dir_x, dir_y) and can_turn((dir_x, dir_y), queued_dir):
            dir_x, dir_y = queued_dir

        new_cell = move_to_cell(grid_x, grid_y, dir_x, dir_y)
        if not new_cell:
            game_over = True
            break

        grid_x, grid_y = new_cell

        # смерть при самопересечении
        if (grid_x, grid_y) in body:
            game_over = True
            break

        body.append((grid_x, grid_y))
        while len(body) > length_cells:
            body.popleft()

        # яблоко
        if (grid_x, grid_y) == apple:
            length_cells += 1
            score += 1
            # новое яблоко не на теле
            while True:
                apple = (randrange(CELLS), randrange(CELLS))
                if apple not in body: break

    # плавная позиция головы
    interp_x = (grid_x - dir_x * (1.0 - progress))
    interp_y = (grid_y - dir_y * (1.0 - progress))
    x = interp_x * SIZE
    y = interp_y * SIZE

    # путь для плавного хвоста
    path.append((x, y))
    trim_path_to_length(path, length_cells * SIZE)

    # === Обновление пуль ===
    for b in bullets[:]:
        if not b["hit"]:
            b["pos"][0] += b["vel"][0] * dt
            b["pos"][1] += b["vel"][1] * dt
            if b["pos"][0] < -50 or b["pos"][0] > RES+50 or b["pos"][1] < -50 or b["pos"][1] > RES+50:
                bullets.remove(b)
        else:
            b["t_hit"] += dt
            b["r"] = BULLET_RADIUS * (1.0 + 0.6 * (b["t_hit"]/BULLET_FADE_TIME))
            b["alpha"] = max(0, int(255 * (1.0 - b["t_hit"]/BULLET_FADE_TIME)))
            if b["t_hit"] >= BULLET_FADE_TIME:
                bullets.remove(b)

    # === Спавн врагов ===
    if now - last_spawn_time >= ENEMY_SPAWN_EVERY and not game_over:
        enemies.append(spawn_enemy())
        last_spawn_time = now

    # === Обновление врагов (A*) ===
    blocked_cells = set(body)
    target_cell = (grid_x, grid_y)
    for e in enemies:
        e.update(dt, target_cell, blocked_cells)

    # === Коллизии пуль и врагов ===
    for b in bullets:
        if b["hit"]: continue
        bx, by = b["pos"]
        for e in enemies:
            if e.rect().collidepoint(bx, by):
                e.hp -= 1
                if e.hp <= 0:
                    enemies.remove(e)
                b["hit"] = True
                b["vel"] = [0.0, 0.0]
                b["alpha"] = 255
                b["t_hit"] = 0.0
                break

    # === Проверка столкновения врагов с головой ===
    headR = head_rect()
    for e in enemies:
        if e.rect().colliderect(headR):
            game_over = True
            break

    # === Рендер ===
    sc.fill((0, 0, 0))

    # Еда — жёлтым
    pygame.draw.rect(sc, (255, 210, 0),
                     (apple[0]*SIZE, apple[1]*SIZE, SIZE, SIZE))

    # Хвост
    draw_fading_path(sc, path, color=(0, 220, 80), fade_to=10, width=SIZE-8)

    # Голова
    pygame.draw.rect(sc, (120, 255, 120), headR)

    # Враги
    for e in enemies:
        pygame.draw.rect(sc, e.color, e.rect())

    # Пули
    for b in bullets:
        col = (255,255,255)
        if b["hit"]:
            s = pygame.Surface((int(b["r"]*2+2), int(b["r"]*2+2)), pygame.SRCALPHA)
            pygame.draw.ellipse(s, (255,255,255,b["alpha"]),
                                (1,1,int(b["r"]*2), int(b["r"]*2)))
            sc.blit(s, (b["pos"][0]-b["r"]-1, b["pos"][1]-b["r"]-1))
        else:
            pygame.draw.ellipse(sc, col,
                                (b["pos"][0]-b["r"], b["pos"][1]-b["r"], b["r"]*2, b["r"]*2))

    # Интерфейс
    fps_txt = font_small.render(f"FPS: {int(clock.get_fps()):>3}", True, (200,200,200))
    pos_txt = font_small.render(f"x,y: {int(x):>3},{int(y):>3}", True, (200,200,200))
    scr_txt = font_small.render(f"score: {score}", True, (200,200,0))
    spd_txt = font_small.render(f"speed: {SPEED_CELLS} cells/s", True, (200,200,200))
    sc.blit(fps_txt, (8, 6))
    sc.blit(pos_txt, (8, 26))
    sc.blit(scr_txt, (8, 46))
    sc.blit(spd_txt, (8, 66))

    if game_over:
        txt = font_big.render("GAME OVER", True, (255, 50, 50))
        sc.blit(txt, (RES//2 - txt.get_width()//2, RES//2 - txt.get_height()//2))
        pygame.display.flip()
        pygame.time.wait(2000)
        pygame.quit()
        raise SystemExit

    pygame.display.flip()
