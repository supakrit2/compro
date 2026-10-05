#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Parking Lot Management System  (ระบบจัดการลานจอดรถ)
Python 3.10+, standard library only.
Bilingual UI: Thai (th) / English (en) - switchable at any time from the main menu.

Binary files (all little-endian, fixed-length records, 20-byte header each):
    data/vehicles.dat   vehicles        <I 20s 10s 15s I>
    data/members.dat    members         <I 30s 15s I I>
    data/parking.dat    parking records <I I I 20s 20s f I>
    data/history.dat    work history    <I I I I I I f>
Text file:
    data/report.txt     summary report (UTF-8, written in the selected language)

Deleted vehicles/members are kept as tombstones (status = 0). Their slots form
a free-list (rebuilt on start-up) and are reused by the next Add.
Data stored in the files is language independent (e.g. vehicle type is always
stored as "Car"/"Motorcycle"); only what is displayed is translated.

Usage:
    python parking_lot.py                    # language menu, then interactive menu
    python parking_lot.py --lang th          # skip the language menu (th / en)
    python parking_lot.py --seed 50          # create 50 demo vehicles + traffic
    python parking_lot.py --report           # write report.txt and exit
    python parking_lot.py --data-dir mydata  # use another folder
"""
import argparse
import math
import os
import random
import re
import struct
import sys
import unicodedata
from collections import Counter
from datetime import datetime, timedelta

# --------------------------------------------------------------------------
# Configuration
# --------------------------------------------------------------------------
APP_VERSION = "1.0"
ENDIAN = "<"                      # little-endian, no padding
TOTAL_SLOTS = 50
RATE_PER_HOUR = 10.0              # THB per started hour
MIN_FEE = 10.0                    # THB
TIME_FMT = "%Y-%m-%d %H:%M:%S" 
   # 19 chars -> fits in 20s
VEHICLE_TYPES = ("Car", "Motorcycle")
PLATE_RE = r"[0-9A-Za-zก-๙ \-]+"
PHONE_RE = r"\+?[0-9\-]{9,15}"

HEADER_FMT = ENDIAN + "4sIIII"    # magic, version, record_size, record_count, next_id
HEADER_SIZE = struct.calcsize(HEADER_FMT)
FORMAT_VERSION = 1

OP_ADD, OP_UPDATE, OP_DELETE, OP_VIEW, OP_ENTRY, OP_EXIT = 1, 2, 3, 4, 5, 6

VEHICLE_FIELDS = [("vehicle_id", "I"), ("plate", "20s"), ("vehicle_type", "10s"),
                  ("brand", "15s"), ("status", "I")]
MEMBER_FIELDS = [("member_id", "I"), ("name", "30s"), ("phone", "15s"),
                 ("vehicle_id", "I"), ("status", "I")]
PARKING_FIELDS = [("parking_id", "I"), ("vehicle_id", "I"), ("slot_no", "I"),
                  ("time_in", "20s"), ("time_out", "20s"), ("fee", "f"), ("status", "I")]
HISTORY_FIELDS = [("ts", "I"), ("op_code", "I"), ("vehicle_id", "I"), ("slot_no", "I"),
                  ("status_after", "I"), ("is_parked_after", "I"), ("fee_after_thb", "f")]

# --------------------------------------------------------------------------
# Translation dictionaries  (every user-visible string lives here)
# Placeholders like {id} are filled by t(key, id=...).
# --------------------------------------------------------------------------
EN = {
    # --- language screen / generic ---
    "main_title": "Parking Lot Management System",
    "lang_th_name": "ภาษาไทย",
    "lang_en_name": "English",
    "select_language": "Select language",
    "invalid_lang_choice": "Invalid choice",
    "exit_program": "Exit",
    "back": "Back",
    "goodbye": "Goodbye.",
    # --- main menu ---
    "m_add": "Add",
    "m_update": "Update",
    "m_delete": "Delete",
    "m_view": "View",
    "m_entry": "Vehicle Entry",
    "m_exit_vehicle": "Vehicle Exit & Payment",
    "m_report": "Generate Report",
    "m_language": "Change Language",
    "m_exit": "Exit",
    "select": "Select: ",
    "invalid_main": "Invalid choice, enter 0-8.",
    # --- entities / sub menus ---
    "vehicle": "Vehicle",
    "member": "Member",
    "ttl_which": "Which data?",
    "e_vehicles": "Vehicles",
    "e_members": "Members",
    "e_parking": "Parking records",
    "ttl_vehicle_type": "Vehicle type",
    "v_single": "Single record",
    "v_all": "All records",
    "v_filter": "Filter",
    "v_stats": "Summary statistics",
    "ttl_filter_vehicles": "Filter vehicles by",
    "f_type": "Type",
    "f_brand": "Brand contains",
    "f_parked": "Currently parked",
    "f_status": "Status (active/deleted)",
    "ttl_filter_parking": "Filter parking records by",
    "f_completed": "Completed",
    "f_vehicle_id": "Vehicle ID",
    # --- prompts ---
    "p_plate": "Plate (e.g. ABC-1234): ",
    "p_phone": "Phone (9-15 digits): ",
    "p_brand": "Brand: ",
    "p_name": "Name: ",
    "p_vehicle_id": "Vehicle ID: ",
    "p_member_id": "Member ID: ",
    "p_id": "ID: ",
    "p_slot": "Slot number (blank = auto): ",
    "yn_hint": "[y/n]",
    "q_show_parked": "Show parked vehicles? (n = not parked)",
    "q_active_only": "Active only? (n = deleted only)",
    "q_active_members": "Active members only? (n = deleted only)",
    "cur_vehicle": "Current: {plate} / {type} / {brand}  (blank = keep)",
    "cur_member": "Current: {name} / {phone} / vehicle {vid}  (blank = keep)",
    "confirm_del_vehicle": "Delete vehicle {id} ({plate})?",
    "confirm_del_member": "Delete member {id} ({name})?",
    # --- input validation ---
    "err_need_int": "Please enter a whole number.",
    "err_range": "Value must be between {lo} and {hi}.",
    "err_min": "Value must be at least {lo}.",
    "err_required": "This field is required.",
    "err_too_long": "Too long (max {max} bytes in UTF-8).",
    "err_yes_no": "Please answer y or n.",
    "hint_plate": "Use letters, digits, space or '-' only.",
    "hint_phone": "Phone must be 9-15 digits (may start with +, may contain -).",
    # --- business errors ---
    "err_vehicle_not_found": "Vehicle {id} not found",
    "err_member_not_found": "Member {id} not found",
    "err_parking_not_found": "Parking record {id} not found",
    "err_plate_exists": "Plate {plate} already exists",
    "err_vehicle_parked_delete": "Vehicle is currently parked - process the exit first",
    "err_already_parked": "Vehicle is already parked",
    "err_lot_full": "Parking lot is full",
    "err_slot_unavailable": "Slot {slot} is not available",
    "err_not_parked": "Vehicle is not currently parked",
    "err_cancelled": "Cancelled",
    # --- file / start-up errors ---
    "err_incomplete_header": "{path}: incomplete header",
    "err_bad_magic": "{path}: bad magic/version (not a valid data file)",
    "err_record_size": "{path}: record size {actual} != expected {expected}",
    "err_bad_status": "{path}: slot {slot} has invalid status {status}",
    "err_dup_id": "{path}: duplicate id {rid}",
    "warn_partial": "[WARN] {path}: dropped {extra} bytes of a partial record",
    "corrupt_notice": "[ERROR] {error}\nFix or delete the damaged file and restart.",
    # --- results ---
    "ok_vehicle_added": "OK: vehicle added with ID {id}",
    "ok_member_added": "OK: member added with ID {id}",
    "ok_vehicle_updated": "OK: vehicle updated",
    "ok_member_updated": "OK: member updated",
    "ok_vehicle_deleted": "OK: vehicle deleted",
    "ok_member_deleted": "OK: member deleted",
    "free_slots_info": "Free slots: {free}/{total}",
    "available_slots": "Available slots: {slots}",
    "ok_parked": "OK: parked in slot {slot} at {time}",
    "ok_exit": "OK: slot {slot} released. In {time_in} / Out {time_out}",
    "fee_line": "Fee: {fee} THB",
    "fee_rate": "Rate: {rate} THB per started hour (minimum {min} THB)",
    "ok_report": "OK: report written to {path}",
    "report_written": "Report written to {path}",
    "seed_skipped": "Data already exists - seed skipped (use a new --data-dir).",
    "seed_done": "Seeded {n} vehicles, {members} members, {parking} parking records.",
    # --- table headers ---
    "col_vehicle_id": "ID",
    "col_member_id": "ID",
    "col_parking_id": "ID",
    "col_vehicle_ref": "Vehicle",
    "col_plate": "Plate",
    "col_type": "Type",
    "col_brand": "Brand",
    "col_slot": "Slot",
    "col_status": "Status",
    "col_parked": "Parked",
    "col_name": "Name",
    "col_phone": "Phone",
    "col_time_in": "Time In",
    "col_time_out": "Time Out",
    "col_fee": "Fee",
    # --- status / values ---
    "status_active": "Active",
    "status_deleted": "Deleted",
    "status_parked": "Parked",
    "status_done": "Done",
    "yes": "Yes",
    "no": "No",
    "type_Car": "Car",
    "type_Motorcycle": "Motorcycle",
    "op_1": "ADD",
    "op_2": "UPDATE",
    "op_3": "DELETE",
    "op_4": "VIEW",
    "op_5": "ENTRY",
    "op_6": "EXIT",
    # --- report ---
    "rpt_title": "Parking Lot Management System - Summary Report",
    "rpt_generated": "Generated At",
    "rpt_version": "App Version",
    "rpt_endian": "Endianness",
    "rpt_encoding": "Encoding",
    "little_endian": "Little-Endian",
    "fixed_length_utf8": "UTF-8 (Fixed-length)",
    "sec_summary": "Summary (Active records only)",
    "r_total_vehicles": "Total Vehicles (records)",
    "r_active_vehicles": "Active Vehicles",
    "r_deleted_vehicles": "Deleted Vehicles",
    "r_currently_parked": "Currently Parked",
    "r_available_vehicles": "Available Vehicles",
    "sec_lot": "Parking Lot Statistics",
    "r_total_slots": "Total Parking Slots",
    "r_occupied": "Occupied Slots",
    "r_available_slots": "Available Slots",
    "sec_parking_records": "Parking Records",
    "r_total_parking_records": "Total Parking Records",
    "r_completed_parking": "Completed Parking",
    "sec_fee": "Fee Statistics (Completed only)",
    "r_min": "Min",
    "r_max": "Max",
    "r_avg": "Avg",
    "sec_by_type": "Vehicles by Type (Active only)",
    "sec_by_brand": "Vehicles by Brand (Active only)",
    "sec_members": "Members",
    "r_total_members": "Total Members",
    "r_active_members": "Active Members",
    "sec_storage": "Storage (binary files)",
    "storage_line": "{count} records ({used} used, {free} free slots)",
    "records_only": "{count} records",
    "sec_recent": "Recent Activity (last 10)",
    "none": "(none)",
    "rpt_vehicle": "vehicle",
    "rpt_slot": "slot",
    "rpt_fee": "fee",
    # --- argparse ---
    "help_desc": "Parking Lot Management System",
    "help_usage": "usage",
    "help_options": "options",
    "help_help": "show this help message and exit",
    "help_data_dir": "folder for .dat/.txt files (default: data)",
    "help_seed": "create N demo vehicles with traffic",
    "help_report": "write 3 report files and exit",
    "help_lang": "UI language: th or en (skips the language menu)",
    "arg_error": "error: {msg}",
}

TH = {
    "main_title": "ระบบจัดการลานจอดรถ",
    "lang_th_name": "ภาษาไทย", "lang_en_name": "English",
    "select_language": "เลือกภาษา", "invalid_lang_choice": "เลือกไม่ถูกต้อง",
    "exit_program": "ออกจากโปรแกรม", "back": "ย้อนกลับ", "goodbye": "จบการทำงาน ขอบคุณที่ใช้ระบบ",
    "m_add": "เพิ่มข้อมูล", "m_update": "แก้ไขข้อมูล", "m_delete": "ลบข้อมูล",
    "m_view": "แสดงข้อมูล", "m_entry": "นำรถเข้าจอด", "m_exit_vehicle": "นำรถออกและชำระเงิน",
    "m_report": "สร้างรายงาน", "m_language": "เปลี่ยนภาษา", "m_exit": "ออกจากโปรแกรม",
    "select": "เลือก: ", "invalid_main": "เลือกไม่ถูกต้อง กรุณาเลือกหมายเลข 0-8",
    "vehicle": "รถ", "member": "สมาชิก", "ttl_which": "ต้องการจัดการข้อมูลประเภทใด",
    "e_vehicles": "ข้อมูลรถ", "e_members": "ข้อมูลสมาชิก", "e_parking": "ประวัติการจอด",
    "ttl_vehicle_type": "เลือกประเภทรถ", "v_single": "แสดงข้อมูลรายการเดียว", "v_all": "แสดงข้อมูลทั้งหมด",
    "v_filter": "ค้นหาและกรองข้อมูล", "v_stats": "แสดงสถิติ",
    "ttl_filter_vehicles": "กรองข้อมูลรถตาม", "f_type": "ประเภทรถ", "f_brand": "ยี่ห้อที่มีคำว่า",
    "f_parked": "สถานะการจอด", "f_status": "สถานะข้อมูล (ใช้งาน/ลบแล้ว)",
    "ttl_filter_parking": "กรองประวัติการจอดตาม", "f_completed": "สถานะเสร็จสิ้น", "f_vehicle_id": "รหัสรถ",
    "p_plate": "เลขทะเบียนรถ (เช่น ABC-1234): ", "p_phone": "เบอร์โทรศัพท์ (9-15 หลัก): ",
    "p_brand": "ยี่ห้อรถ: ", "p_name": "ชื่อสมาชิก: ", "p_vehicle_id": "รหัสรถ: ",
    "p_member_id": "รหัสสมาชิก: ", "p_id": "รหัสข้อมูล: ",
    "p_slot": "หมายเลขช่องจอด (เว้นว่างเพื่อให้ระบบเลือกอัตโนมัติ): ",
    "yn_hint": "[y=ใช่ / n=ไม่ใช่]", "q_show_parked": "แสดงเฉพาะรถที่กำลังจอดหรือไม่? (n = รถที่ไม่ได้จอด)",
    "q_active_only": "แสดงเฉพาะข้อมูลที่ใช้งานอยู่หรือไม่? (n = ข้อมูลที่ลบแล้ว)",
    "q_active_members": "แสดงเฉพาะสมาชิกที่ใช้งานอยู่หรือไม่? (n = สมาชิกที่ลบแล้ว)",
    "cur_vehicle": "ข้อมูลปัจจุบัน: {plate} / {type} / {brand} (เว้นว่างเพื่อคงข้อมูลเดิม)",
    "cur_member": "ข้อมูลปัจจุบัน: {name} / {phone} / รถรหัส {vid} (เว้นว่างเพื่อคงข้อมูลเดิม)",
    "confirm_del_vehicle": "ยืนยันการลบรถรหัส {id} ({plate}) หรือไม่?",
    "confirm_del_member": "ยืนยันการลบสมาชิกรหัส {id} ({name}) หรือไม่?",
    "err_need_int": "กรุณาป้อนตัวเลขจำนวนเต็ม", "err_range": "ค่าต้องอยู่ระหว่าง {lo} ถึง {hi}",
    "err_min": "ค่าต้องไม่น้อยกว่า {lo}", "err_required": "กรุณากรอกข้อมูลในช่องนี้",
    "err_too_long": "ข้อมูลยาวเกินกำหนด (สูงสุด {max} ไบต์ใน UTF-8)",
    "err_yes_no": "กรุณาตอบ y/n หรือ ใช่/ไม่ใช่", "hint_plate": "ใช้ตัวอักษร ตัวเลข ช่องว่าง หรือเครื่องหมาย - เท่านั้น",
    "hint_phone": "เบอร์โทรต้องมี 9-15 หลัก สามารถขึ้นต้นด้วย + และมีเครื่องหมาย - ได้",
    "err_vehicle_not_found": "ไม่พบรถรหัส {id}", "err_member_not_found": "ไม่พบสมาชิกรหัส {id}",
    "err_parking_not_found": "ไม่พบประวัติการจอดรหัส {id}", "err_plate_exists": "เลขทะเบียน {plate} มีอยู่ในระบบแล้ว",
    "err_vehicle_parked_delete": "รถคันนี้กำลังจอดอยู่ กรุณานำรถออกก่อนจึงจะลบได้",
    "err_already_parked": "รถคันนี้กำลังจอดอยู่แล้ว", "err_lot_full": "ลานจอดรถเต็ม ไม่มีช่องว่าง",
    "err_slot_unavailable": "ช่องจอด {slot} ไม่ว่าง กรุณาเลือกช่องอื่น", "err_not_parked": "รถคันนี้ไม่ได้กำลังจอดอยู่",
    "err_cancelled": "ยกเลิกการทำรายการแล้ว",
    "err_incomplete_header": "{path}: ส่วนหัวไฟล์ไม่สมบูรณ์", "err_bad_magic": "{path}: รูปแบบหรือเวอร์ชันไฟล์ไม่ถูกต้อง",
    "err_record_size": "{path}: ขนาดข้อมูล {actual} ไม่ตรงกับที่กำหนด {expected}",
    "err_bad_status": "{path}: ช่องข้อมูลที่ {slot} มีสถานะไม่ถูกต้อง {status}", "err_dup_id": "{path}: พบข้อมูลรหัสซ้ำ {rid}",
    "warn_partial": "[คำเตือน] {path}: พบข้อมูลไม่ครบ 1 รายการ จึงตัดออก {extra} ไบต์",
    "corrupt_notice": "[ผิดพลาด] {error}\nกรุณาตรวจสอบหรือลบไฟล์ที่เสียหาย แล้วเปิดโปรแกรมใหม่",
    "ok_vehicle_added": "เพิ่มข้อมูลรถสำเร็จ รหัสรถ: {id}", "ok_member_added": "เพิ่มข้อมูลสมาชิกสำเร็จ รหัสสมาชิก: {id}",
    "ok_vehicle_updated": "แก้ไขข้อมูลรถสำเร็จ", "ok_member_updated": "แก้ไขข้อมูลสมาชิกสำเร็จ",
    "ok_vehicle_deleted": "ลบข้อมูลรถสำเร็จ", "ok_member_deleted": "ลบข้อมูลสมาชิกสำเร็จ",
    "free_slots_info": "ช่องจอดว่าง {free} จากทั้งหมด {total} ช่อง", "available_slots": "ช่องจอดที่ว่าง: {slots}",
    "ok_parked": "นำรถเข้าจอดสำเร็จ ช่องที่ {slot} เวลา {time}",
    "ok_exit": "นำรถออกสำเร็จ ช่องที่ {slot} | เข้า {time_in} | ออก {time_out}",
    "fee_line": "ค่าจอดรถ: {fee} บาท",
    "fee_rate": "อัตราค่าจอด: {rate} บาทต่อชั่วโมง (เศษชั่วโมงคิดเป็น 1 ชั่วโมง, ขั้นต่ำ {min} บาท)",
    "ok_report": "สร้างรายงานสำเร็จ: {path}", "report_written": "สร้างรายงานแล้ว: {path}",
    "seed_skipped": "มีข้อมูลอยู่แล้ว จึงข้ามการสร้างข้อมูลตัวอย่าง (หากต้องการสร้างใหม่ให้ใช้ --data-dir ใหม่)",
    "seed_done": "สร้างข้อมูลตัวอย่างสำเร็จ: รถ {n} คัน, สมาชิก {members} คน, ประวัติการจอด {parking} รายการ",
    "col_vehicle_id": "รหัสรถ", "col_member_id": "รหัสสมาชิก", "col_parking_id": "รหัสการจอด", "col_vehicle_ref": "รหัสรถ",
    "col_plate": "เลขทะเบียน", "col_type": "ประเภทรถ", "col_brand": "ยี่ห้อ", "col_slot": "ช่องจอด",
    "col_status": "สถานะ", "col_parked": "กำลังจอด", "col_name": "ชื่อ", "col_phone": "เบอร์โทรศัพท์",
    "col_time_in": "เวลาเข้า", "col_time_out": "เวลาออก", "col_fee": "ค่าจอด (บาท)",
    "status_active": "ใช้งาน", "status_deleted": "ลบแล้ว", "status_parked": "กำลังจอด", "status_done": "เสร็จสิ้น",
    "yes": "ใช่", "no": "ไม่ใช่", "type_Car": "รถยนต์", "type_Motorcycle": "รถจักรยานยนต์",
    "op_1": "เพิ่มข้อมูล", "op_2": "แก้ไขข้อมูล", "op_3": "ลบข้อมูล", "op_4": "ดูข้อมูล", "op_5": "รถเข้า", "op_6": "รถออก",
    "rpt_title": "รายงานสรุประบบจัดการลานจอดรถ", "rpt_generated": "วันที่และเวลาที่สร้างรายงาน", "rpt_version": "เวอร์ชันโปรแกรม",
    "rpt_endian": "รูปแบบการจัดเก็บไบต์", "rpt_encoding": "รูปแบบการเข้ารหัส", "little_endian": "Little-Endian",
    "fixed_length_utf8": "UTF-8 (ข้อมูลความยาวคงที่)", "sec_summary": "1. สรุปข้อมูลรถ",
    "r_total_vehicles": "จำนวนรถทั้งหมด", "r_active_vehicles": "จำนวนรถที่ใช้งานอยู่", "r_deleted_vehicles": "จำนวนรถที่ลบแล้ว",
    "r_currently_parked": "จำนวนรถที่กำลังจอด", "r_available_vehicles": "จำนวนรถที่ไม่ได้จอด",
    "sec_lot": "2. สรุปการใช้ช่องจอด", "r_total_slots": "จำนวนช่องจอดทั้งหมด", "r_occupied": "จำนวนช่องที่ถูกใช้งาน", "r_available_slots": "จำนวนช่องว่าง",
    "sec_parking_records": "3. สรุปประวัติการจอด", "r_total_parking_records": "จำนวนประวัติการจอดทั้งหมด",
    "r_completed_parking": "จำนวนรายการที่จอดเสร็จสิ้น", "sec_fee": "4. สถิติค่าจอดรถ (เฉพาะรายการที่เสร็จสิ้น)",
    "r_min": "ค่าจอดต่ำสุด", "r_max": "ค่าจอดสูงสุด", "r_avg": "ค่าจอดเฉลี่ย",
    "sec_by_type": "5. จำนวนรถแยกตามประเภท", "sec_by_brand": "6. จำนวนรถแยกตามยี่ห้อ", "sec_members": "7. ข้อมูลสมาชิก",
    "r_total_members": "จำนวนสมาชิกทั้งหมด", "r_active_members": "จำนวนสมาชิกที่ใช้งานอยู่", "sec_storage": "8. ข้อมูลการจัดเก็บไฟล์ไบนารี",
    "storage_line": "{count} รายการ (ใช้งาน {used} ช่อง, ช่องว่าง {free} ช่อง)", "records_only": "{count} รายการ",
    "sec_recent": "9. กิจกรรมล่าสุด (10 รายการ)", "none": "(ไม่มีข้อมูล)", "rpt_vehicle": "รถ", "rpt_slot": "ช่อง", "rpt_fee": "ค่าจอด",
    "help_desc": "ระบบจัดการลานจอดรถ", "help_usage": "วิธีใช้งาน", "help_options": "ตัวเลือก", "help_help": "แสดงวิธีใช้แล้วออกจากโปรแกรม",
    "help_data_dir": "โฟลเดอร์สำหรับเก็บไฟล์ .dat และ .txt (ค่าเริ่มต้น: data)",
    "help_seed": "สร้างข้อมูลรถตัวอย่าง N คันพร้อมประวัติการเข้าออก", "help_report": "สร้างรายงาน 3 ไฟล์แล้วออกจากโปรแกรม",
    "help_lang": "ภาษาของโปรแกรม: th หรือ en (ข้ามหน้าสำหรับเลือกภาษา)", "arg_error": "ข้อผิดพลาด: {msg}",
}


TRANSLATIONS = {"th": TH, "en": EN}
language = "th"                   # current UI language: "th" or "en"
ADMIN_CODE = "0012"
current_role = None
current_member_id = None

# Common vehicle brands. The stored vehicle record format is unchanged.
VEHICLE_BRANDS = ["Toyota", "Honda", "Nissan", "Mazda", "Mitsubishi", "Isuzu", "Suzuki", "Ford", "BMW", "Mercedes-Benz", "Other"]


def set_language(code):
    global language
    if code not in TRANSLATIONS:
        raise ValueError(f"unsupported language: {code}")
    language = code


def t(key, **params):
    """Return the text for `key` in the current language (placeholders filled)."""
    text = TRANSLATIONS[language].get(key)
    if text is None:                              # safety net: never crash on a missing key
        text = TRANSLATIONS["en"].get(key, key)
    return text.format(**params) if params else text


def bi(key):
    """Bilingual text 'Thai / English' (used only on the language screen)."""
    return f"{TH[key]} / {EN[key]}"


EN.update({
    "rpt_members_title": "Parking Lot Management System - Members Report",
    "rpt_parking_title": "Parking Lot Management System - Parking Records Report",
    "rpt_summary_end": "End of Report - Summary",
    "sec_member_summary": "Member Summary",
    "r_deleted_members": "Deleted Members",
    "r_members_parked": "Members With Vehicle Parked Now",
    "r_members_no_vehicle": "Active Members Without Active Vehicle",
    "sec_member_by_type": "Members by Vehicle Type (Active only)",
    "sec_parking_summary": "Parking Summary",
    "r_revenue": "Total Revenue (THB)",
    "r_avg_duration": "Average Duration (hours)",
    "sec_revenue_type": "Revenue by Vehicle Type (Completed only)",
    "sec_top_slots": "Most Used Slots (top 5)",
    "r_times": "{n} times",
})
TH.update({
    "rpt_members_title": "รายงานสมาชิก ระบบจัดการลานจอดรถ",
    "rpt_parking_title": "รายงานประวัติการจอด ระบบจัดการลานจอดรถ",
    "rpt_summary_end": "สรุปท้ายรายงาน",
    "sec_member_summary": "สรุปสมาชิก",
    "r_deleted_members": "สมาชิกที่ลบแล้ว",
    "r_members_parked": "สมาชิกที่รถกำลังจอดอยู่",
    "r_members_no_vehicle": "สมาชิกที่ใช้งานแต่ไม่มีรถที่ใช้งาน",
    "sec_member_by_type": "สมาชิกแยกตามประเภทรถ (เฉพาะที่ใช้งาน)",
    "sec_parking_summary": "สรุปการจอด",
    "r_revenue": "รายได้รวม (บาท)",
    "r_avg_duration": "ระยะเวลาจอดเฉลี่ย (ชั่วโมง)",
    "sec_revenue_type": "รายได้แยกตามประเภทรถ (เฉพาะที่เสร็จสิ้น)",
    "sec_top_slots": "ช่องจอดที่ใช้บ่อยที่สุด (5 อันดับ)",
    "r_times": "{n} ครั้ง",
})

# เพิ่มข้อความที่ใช้ในหน้าเข้าสู่ระบบ/สมัครสมาชิก/รายงานให้ครบทั้งไทยและอังกฤษ
EN.update({
    "role_title": "Select User Type",
    "role_admin": "Administrator",
    "role_user": "Member / User",
    "role_register": "Register New Member",
    "p_admin_code": "Administrator code: ",
    "p_login_member": "Member ID: ",
    "login_failed": "Incorrect code or member ID",
    "register_title": "Register New Member",
    "register_success": "Registration successful. Member ID: {id}",
    "user_title": "Member Menu",
    "user_vehicle_only": "My vehicle information",
    "m_brand_select": "Select Vehicle Brand",
    "brand_other": "Other",
    "p_brand_other": "Enter vehicle brand: ",
})

TH.update({
    "role_title": "เลือกประเภทผู้ใช้งาน",
    "role_admin": "ผู้ดูแลระบบ",
    "role_user": "สมาชิก / ผู้ใช้งาน",
    "role_register": "สมัครสมาชิกใหม่",
    "p_admin_code": "รหัสผู้ดูแลระบบ: ",
    "p_login_member": "รหัสสมาชิก: ",
    "login_failed": "รหัสไม่ถูกต้อง หรือไม่พบรหัสสมาชิก",
    "register_title": "สมัครสมาชิกใหม่",
    "register_success": "สมัครสมาชิกสำเร็จ รหัสสมาชิก: {id}",
    "user_title": "เมนูสมาชิก",
    "user_vehicle_only": "ข้อมูลรถของฉัน",
    "m_brand_select": "เลือกยี่ห้อรถ",
    "brand_other": "อื่น ๆ",
    "p_brand_other": "กรอกยี่ห้อรถ: ",
})




class CorruptFileError(Exception):
    def __init__(self, key, **params):
        super().__init__(key)
        self.key, self.params = key, params

    def __str__(self):
        return t(self.key, **self.params)


class AppError(Exception):
    """Business-rule / validation error shown to the user (translated when displayed)."""
    def __init__(self, key, **params):
        super().__init__(key)
        self.key, self.params = key, params

    def __str__(self):
        return t(self.key, **self.params)


# --------------------------------------------------------------------------
# Low-level fixed-length binary table  (format unchanged)
# --------------------------------------------------------------------------
def fit(text, n):
    """Encode to UTF-8 and cut to at most n bytes without splitting a character."""
    return text.encode("utf-8")[:n].decode("utf-8", "ignore").encode("utf-8")


class Table:
    def __init__(self, path, magic, fields, id_field=None, first_id=1, reusable=False):
        self.path, self.magic, self.fields = path, magic, fields
        self.st = struct.Struct(ENDIAN + "".join(code for _, code in fields))
        self.id_field, self.first_id, self.reusable = id_field, first_id, reusable
        self.index, self.free = {}, []          # id -> slot, list of free slots
        self.count, self.next_id = 0, first_id
        self._open()

    # ---- open / validate / recover ----
    def _open(self):
        if not os.path.exists(self.path):
            with open(self.path, "wb") as f:
                f.write(struct.pack(HEADER_FMT, self.magic, FORMAT_VERSION,
                                    self.st.size, 0, self.first_id))
        self.f = open(self.path, "r+b")
        raw = self.f.read(HEADER_SIZE)
        if len(raw) < HEADER_SIZE:
            raise CorruptFileError("err_incomplete_header", path=self.path)
        magic, ver, rsize, _cnt, nid = struct.unpack(HEADER_FMT, raw)
        if magic != self.magic or ver != FORMAT_VERSION:
            raise CorruptFileError("err_bad_magic", path=self.path)
        if rsize != self.st.size:
            raise CorruptFileError("err_record_size", path=self.path,
                                   actual=rsize, expected=self.st.size)
        body = os.fstat(self.f.fileno()).st_size - HEADER_SIZE
        n, extra = divmod(body, self.st.size)
        if extra:                                # half-written last record
            print(t("warn_partial", path=self.path, extra=extra))
            self.f.truncate(HEADER_SIZE + n * self.st.size)
        self.count, self.next_id = n, nid        # record count comes from file size
        self._rebuild()
        self._write_header()

    def _rebuild(self):
        self.index.clear()
        self.free.clear()
        for slot, rec in enumerate(self.records()):
            if "status" in rec and rec["status"] not in (0, 1):
                raise CorruptFileError("err_bad_status", path=self.path,
                                       slot=slot, status=rec["status"])
            if self.id_field:
                rid = rec[self.id_field]
                if rid in self.index:
                    raise CorruptFileError("err_dup_id", path=self.path, rid=rid)
                self.index[rid] = slot
                self.next_id = max(self.next_id, rid + 1)
            if self.reusable and rec["status"] == 0:
                self.free.append(slot)

    # ---- pack / unpack ----
    def _pack(self, rec):
        vals = []
        for name, code in self.fields:
            v = rec[name]
            if code.endswith("s"):
                v = fit(str(v), int(code[:-1]))
            vals.append(v)
        return self.st.pack(*vals)

    def _unpack(self, raw):
        rec = {}
        for (name, code), v in zip(self.fields, self.st.unpack(raw)):
            if code.endswith("s"):
                v = v.rstrip(b"\x00").decode("utf-8", errors="replace")
            rec[name] = v
        return rec

    # ---- raw I/O ----
    def _write_header(self):
        self.f.seek(0)
        self.f.write(struct.pack(HEADER_FMT, self.magic, FORMAT_VERSION,
                                 self.st.size, self.count, self.next_id))
        self._sync()

    def _write(self, slot, rec):
        self.f.seek(HEADER_SIZE + slot * self.st.size)
        self.f.write(self._pack(rec))
        self._sync()

    def _read(self, slot):
        self.f.seek(HEADER_SIZE + slot * self.st.size)
        return self._unpack(self.f.read(self.st.size))

    def _sync(self):
        self.f.flush()
        os.fsync(self.f.fileno())

    # ---- public API ----
    def records(self):
        self.f.seek(HEADER_SIZE)
        data = self.f.read(self.count * self.st.size)
        sz = self.st.size
        return [self._unpack(data[i * sz:(i + 1) * sz]) for i in range(self.count)]

    def get(self, rid):
        slot = self.index.get(rid)
        return None if slot is None else self._read(slot)

    def insert(self, rec):
        if self.id_field:
            rec[self.id_field] = self.next_id
            self.next_id += 1
        if self.reusable and self.free:
            slot = self.free.pop(0)              # reuse a deleted slot
            if self.id_field:
                self.index.pop(self._read(slot)[self.id_field], None)
        else:
            slot = self.count
            self.count += 1
        self._write(slot, rec)                   # record first, then header
        self._write_header()
        if self.id_field:
            self.index[rec[self.id_field]] = slot
        return rec

    def update(self, rec):
        self._write(self.index[rec[self.id_field]], rec)

    def delete(self, rid):
        rec = self.get(rid)
        rec["status"] = 0
        self.update(rec)
        if self.reusable:
            self.free.append(self.index[rid])

    def close(self):
        if not self.f.closed:
            self._sync()
            self.f.close()


# --------------------------------------------------------------------------
# Business logic  (unchanged except that errors carry translation keys)
# --------------------------------------------------------------------------
def calc_fee(t_in, t_out):
    seconds = max(0.0, (t_out - t_in).total_seconds())
    hours = max(1, math.ceil(seconds / 3600))
    return max(MIN_FEE, hours * RATE_PER_HOUR)


class ParkingSystem:
    def __init__(self, data_dir):
        os.makedirs(data_dir, exist_ok=True)
        p = lambda name: os.path.join(data_dir, name)
        self.report_path = p("report_summary.txt")
        self.report_members_path = p("report_members.txt")
        self.report_parking_path = p("report_parking.txt")
        self.vehicles = Table(p("vehicles.dat"), b"VEHC", VEHICLE_FIELDS, "vehicle_id", 1001, True)
        self.members = Table(p("members.dat"), b"MEMB", MEMBER_FIELDS, "member_id", 5001, True)
        self.parking = Table(p("parking.dat"), b"PARK", PARKING_FIELDS, "parking_id", 1, False)
        self.history = Table(p("history.dat"), b"HIST", HISTORY_FIELDS)

    def close(self):
        for t_ in (self.vehicles, self.members, self.parking, self.history):
            t_.close()

    def _log(self, op, vid=0, slot=0, status=0, parked=0, fee=0.0, now=None):
        now = now or datetime.now()
        self.history.insert({"ts": int(now.timestamp()), "op_code": op, "vehicle_id": vid,
                             "slot_no": slot, "status_after": status,
                             "is_parked_after": parked, "fee_after_thb": fee})

    # ---- helpers ----
    def parked_map(self):
        return {r["vehicle_id"]: r for r in self.parking.records() if r["status"] == 1}

    def free_slots(self):
        used = {r["slot_no"] for r in self.parking.records() if r["status"] == 1}
        return [s for s in range(1, TOTAL_SLOTS + 1) if s not in used]

    def active_vehicle(self, vid):
        rec = self.vehicles.get(vid)
        if not rec or rec["status"] == 0:
            raise AppError("err_vehicle_not_found", id=vid)
        return rec

    def active_member(self, mid):
        rec = self.members.get(mid)
        if not rec or rec["status"] == 0:
            raise AppError("err_member_not_found", id=mid)
        return rec

    def _plate_taken(self, plate, ignore_id=None):
        return any(v["status"] == 1 and v["plate"] == plate and v["vehicle_id"] != ignore_id
                   for v in self.vehicles.records())

    # ---- vehicles ----
    def add_vehicle(self, plate, vtype, brand, now=None):
        plate = plate.upper()
        if self._plate_taken(plate):
            raise AppError("err_plate_exists", plate=plate)
        rec = self.vehicles.insert({"vehicle_id": 0, "plate": plate, "vehicle_type": vtype,
                                    "brand": brand, "status": 1})
        self._log(OP_ADD, rec["vehicle_id"], 0, 1, 0, 0.0, now)
        return rec

    def update_vehicle(self, vid, plate=None, vtype=None, brand=None):
        rec = self.active_vehicle(vid)
        if plate:
            plate = plate.upper()
            if self._plate_taken(plate, ignore_id=vid):
                raise AppError("err_plate_exists", plate=plate)
            rec["plate"] = plate
        if vtype:
            rec["vehicle_type"] = vtype
        if brand:
            rec["brand"] = brand
        self.vehicles.update(rec)
        p = self.parked_map().get(vid)
        self._log(OP_UPDATE, vid, p["slot_no"] if p else 0, 1, 1 if p else 0)
        return rec

    def delete_vehicle(self, vid):
        self.active_vehicle(vid)
        if vid in self.parked_map():
            raise AppError("err_vehicle_parked_delete")
        self.vehicles.delete(vid)
        self._log(OP_DELETE, vid, 0, 0, 0)

    def view_vehicle(self, vid):
        rec = self.vehicles.get(vid)
        if not rec:
            raise AppError("err_vehicle_not_found", id=vid)
        p = self.parked_map().get(vid)
        self._log(OP_VIEW, vid, p["slot_no"] if p else 0, rec["status"], 1 if p else 0)
        return rec

    # ---- members ----
    def add_member(self, name, phone, vid, now=None):
        self.active_vehicle(vid)
        rec = self.members.insert({"member_id": 0, "name": name, "phone": phone,
                                   "vehicle_id": vid, "status": 1})
        self._log(OP_ADD, vid, 0, 1, 1 if vid in self.parked_map() else 0, 0.0, now)
        return rec

    def update_member(self, mid, name=None, phone=None, vid=None):
        rec = self.active_member(mid)
        if vid is not None:
            self.active_vehicle(vid)
            rec["vehicle_id"] = vid
        if name:
            rec["name"] = name
        if phone:
            rec["phone"] = phone
        self.members.update(rec)
        self._log(OP_UPDATE, rec["vehicle_id"], 0, 1, 1 if rec["vehicle_id"] in self.parked_map() else 0)
        return rec

    def delete_member(self, mid):
        rec = self.active_member(mid)
        self.members.delete(mid)
        self._log(OP_DELETE, rec["vehicle_id"], 0, 0, 0)

    # ---- parking ----
    def enter(self, vid, slot=None, now=None):
        now = now or datetime.now()
        self.active_vehicle(vid)

        # Read active parking records once instead of calling parked_map() and
        # free_slots() separately. This avoids scanning parking.dat twice.
        active_records = [r for r in self.parking.records() if r["status"] == 1]
        if any(r["vehicle_id"] == vid for r in active_records):
            raise AppError("err_already_parked")

        used_slots = {r["slot_no"] for r in active_records}
        free = [s for s in range(1, TOTAL_SLOTS + 1) if s not in used_slots]
        if not free:
            raise AppError("err_lot_full")
        if slot is None:
            slot = free[0]
        elif slot not in free:
            raise AppError("err_slot_unavailable", slot=slot)

        rec = self.parking.insert({"parking_id": 0, "vehicle_id": vid, "slot_no": slot,
                                   "time_in": now.strftime(TIME_FMT), "time_out": "",
                                   "fee": 0.0, "status": 1})
        self._log(OP_ENTRY, vid, slot, 1, 1, 0.0, now)
        return rec

    def leave(self, vid, now=None):
        now = now or datetime.now()
        rec = self.parked_map().get(vid)
        if not rec:
            raise AppError("err_not_parked")
        t_in = datetime.strptime(rec["time_in"], TIME_FMT)
        rec["time_out"] = now.strftime(TIME_FMT)
        rec["fee"] = calc_fee(t_in, now)
        rec["status"] = 0
        self.parking.update(rec)
        self._log(OP_EXIT, vid, rec["slot_no"], 1, 0, rec["fee"], now)
        return rec


# --------------------------------------------------------------------------
# Tables / report text  (language-aware)
# --------------------------------------------------------------------------
def dwidth(s):
    """Display width: Thai combining vowels/tone marks take no column."""
    w = 0
    for ch in s:
        if unicodedata.category(ch) in ("Mn", "Me", "Cf"):
            continue
        w += 2 if unicodedata.east_asian_width(ch) in ("W", "F") else 1
    return w


def pad(s, width):
    return s + " " * (width - dwidth(s))


def veh_head():
    return [t("col_vehicle_id"), t("col_plate"), t("col_type"), t("col_brand"),
            t("col_slot"), t("col_status"), t("col_parked")]


def mem_head():
    return [t("col_member_id"), t("col_name"), t("col_phone"),
            t("col_vehicle_ref"), t("col_status")]


def prk_head():
    return [t("col_parking_id"), t("col_vehicle_ref"), t("col_slot"), t("col_time_in"),
            t("col_time_out"), t("col_fee"), t("col_status")]


def status_label(v):
    return t("status_active") if v == 1 else t("status_deleted")


def type_label(v):
    return TRANSLATIONS[language].get("type_" + v, v)


def op_name(code):
    return TRANSLATIONS[language].get(f"op_{code}", "?")


def text_table(headers, rows):
    rows = [[str(c) for c in r] for r in rows]
    widths = [max(dwidth(c) for c in col) for col in zip(*([headers] + rows))]
    sep = "+" + "+".join("-" * (w + 2) for w in widths) + "+"
    line = lambda cells: "| " + " | ".join(pad(c, w) for c, w in zip(cells, widths)) + " |"
    return "\n".join([sep, line(headers), sep] + [line(r) for r in rows] + [sep])


def vehicle_rows(vehicles, parked):
    rows = []
    for v in vehicles:
        p = parked.get(v["vehicle_id"]) if v["status"] == 1 else None
        rows.append([v["vehicle_id"], v["plate"], type_label(v["vehicle_type"]), v["brand"],
                     p["slot_no"] if p else "-", status_label(v["status"]),
                     t("yes") if p else t("no")])
    return rows


def member_rows(members):
    return [[m["member_id"], m["name"], m["phone"], m["vehicle_id"], status_label(m["status"])]
            for m in members]


def parking_rows(records):
    return [[r["parking_id"], r["vehicle_id"], r["slot_no"], r["time_in"], r["time_out"] or "-",
             f"{r['fee']:.2f}", t("status_parked") if r["status"] == 1 else t("status_done")]
            for r in records]


def aligned(pairs):
    w = max(dwidth(k) for k, _ in pairs)
    return [f"{pad(k, w)} : {v}" for k, v in pairs]


def kv_block(pairs):
    return ["- " + line for line in aligned(pairs)]


def section(title, pairs):
    return [title, ""] + (kv_block(pairs) if pairs else ["- " + t("none")]) + [""]


def build_report(s, now, with_table=True, with_header=True):
    vehicles = sorted(s.vehicles.records(), key=lambda r: r["vehicle_id"])
    members = s.members.records()
    parking = s.parking.records()
    history = s.history.records()
    parked = {r["vehicle_id"]: r for r in parking if r["status"] == 1}
    active = [v for v in vehicles if v["status"] == 1]
    parked_active = [v for v in active if v["vehicle_id"] in parked]
    completed = [r for r in parking if r["status"] == 0]
    fees = [r["fee"] for r in completed]

    z = now.strftime("%z") or "+0000"
    out = []
    if with_header:
        out.append(t("rpt_title"))
        out += aligned([(t("rpt_generated"), f"{now.strftime(TIME_FMT)} ({z[:3]}:{z[3:]})"),
                        (t("rpt_version"), APP_VERSION),
                        (t("rpt_endian"), t("little_endian")),
                        (t("rpt_encoding"), t("fixed_length_utf8"))])
        out.append("")
    if with_table:
        out += [text_table(veh_head(), vehicle_rows(vehicles, parked)), ""]

    out += section(t("sec_summary"), [
        (t("r_total_vehicles"), len(vehicles)),
        (t("r_active_vehicles"), len(active)),
        (t("r_deleted_vehicles"), len(vehicles) - len(active)),
        (t("r_currently_parked"), len(parked_active)),
        (t("r_available_vehicles"), len(active) - len(parked_active))])
    out += section(t("sec_lot"), [
        (t("r_total_slots"), TOTAL_SLOTS),
        (t("r_occupied"), len(parked)),
        (t("r_available_slots"), TOTAL_SLOTS - len(parked))])
    out += section(t("sec_parking_records"), [
        (t("r_total_parking_records"), len(parking)),
        (t("r_completed_parking"), len(completed)),
        (t("r_currently_parked"), len(parked))])
    out += section(t("sec_fee"), [
        (t("r_min"), f"{min(fees):.2f}"), (t("r_max"), f"{max(fees):.2f}"),
        (t("r_avg"), f"{sum(fees) / len(fees):.2f}")] if fees else [])
    out += section(t("sec_by_type"),
                   [(type_label(k), n) for k, n in
                    sorted(Counter(v["vehicle_type"] for v in active).items())])
    out += section(t("sec_by_brand"),
                   sorted(Counter(v["brand"] for v in active).items()))
    out += section(t("sec_members"), [
        (t("r_total_members"), len(members)),
        (t("r_active_members"), sum(1 for m in members if m["status"] == 1))])

    def storage(name, table):
        return (name, t("storage_line", count=table.count,
                        used=table.count - len(table.free), free=len(table.free)))
    out += section(t("sec_storage"), [
        storage("vehicles.dat", s.vehicles), storage("members.dat", s.members),
        ("parking.dat", t("records_only", count=s.parking.count)),
        ("history.dat", t("records_only", count=s.history.count))])

    out += [t("sec_recent"), ""]
    for h in reversed(history[-10:]):
        ts = datetime.fromtimestamp(h["ts"]).strftime(TIME_FMT)
        out.append(f"- {ts} | {pad(op_name(h['op_code']), 8)} | {t('rpt_vehicle')} {h['vehicle_id']}"
                   f" | {t('rpt_slot')} {h['slot_no'] or '-'} | {t('rpt_fee')} {h['fee_after_thb']:.2f}")
    if not history:
        out.append("- " + t("none"))
    return "\n".join(out) + "\n"


def _write_report(path, text):
    """Write one UTF-8 text report and return its path."""
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)
    return path


def build_members_report(s, now):
    members = sorted(s.members.records(), key=lambda r: r["member_id"])
    active_members = [m for m in members if m["status"] == 1]
    parked = {r["vehicle_id"] for r in s.parking.records() if r["status"] == 1}
    active_vehicle_ids = {v["vehicle_id"] for v in s.vehicles.records() if v["status"] == 1}
    parked_members = [m for m in active_members if m["vehicle_id"] in parked]
    no_vehicle_members = [m for m in active_members if m["vehicle_id"] not in active_vehicle_ids]

    out = [t("rpt_members_title"), ""]
    out += aligned([
        (t("rpt_generated"), now.strftime(TIME_FMT)),
        (t("rpt_version"), APP_VERSION),
        (t("rpt_encoding"), t("fixed_length_utf8")),
    ])
    out += ["", t("sec_member_by_type"), ""]
    out += [text_table(mem_head(), member_rows(members)), ""]
    out += section(t("sec_member_summary"), [
        (t("r_total_members"), len(members)),
        (t("r_active_members"), len(active_members)),
        (t("r_deleted_members"), len(members) - len(active_members)),
        (t("r_members_parked"), len(parked_members)),
        (t("r_members_no_vehicle"), len(no_vehicle_members)),
    ])
    out += [t("sec_recent"), "", t("none") if not members else "- " + t("r_total_members") + f": {len(members)}", ""]
    out += [t("rpt_summary_end"), ""]
    return "\n".join(out)


def build_parking_report(s, now):
    records = sorted(s.parking.records(), key=lambda r: r["parking_id"])
    completed = [r for r in records if r["status"] == 0]
    active = [r for r in records if r["status"] == 1]
    fees = [r["fee"] for r in completed]
    revenue = sum(fees)
    avg_hours = 0.0
    durations = []
    for r in completed:
        if r["time_in"] and r["time_out"]:
            try:
                tin = datetime.strptime(r["time_in"], TIME_FMT)
                tout = datetime.strptime(r["time_out"], TIME_FMT)
                durations.append(max(0.0, (tout - tin).total_seconds() / 3600))
            except ValueError:
                pass
    if durations:
        avg_hours = sum(durations) / len(durations)

    out = [t("rpt_parking_title"), ""]
    out += aligned([
        (t("rpt_generated"), now.strftime(TIME_FMT)),
        (t("rpt_version"), APP_VERSION),
        (t("rpt_encoding"), t("fixed_length_utf8")),
    ])
    out += ["", text_table(prk_head(), parking_rows(records)), ""]
    out += section(t("sec_parking_summary"), [
        (t("r_total_parking_records"), len(records)),
        (t("r_completed_parking"), len(completed)),
        (t("r_currently_parked"), len(active)),
        (t("r_revenue"), f"{revenue:.2f}"),
        (t("r_avg_duration"), f"{avg_hours:.2f}"),
    ])
    vehicle_type_by_id = {v["vehicle_id"]: v["vehicle_type"] for v in s.vehicles.records()}
    revenue_by_type = {}
    for r in completed:
        vtype = vehicle_type_by_id.get(r["vehicle_id"])
        if vtype is not None:
            revenue_by_type[vtype] = revenue_by_type.get(vtype, 0.0) + r["fee"]
    out += section(t("sec_revenue_type"), [
        (type_label(k), f"{v:.2f}") for k, v in sorted(revenue_by_type.items())
    ])
    out += [t("rpt_summary_end"), ""]
    return "\n".join(out)


def generate_report(s):
    """Create 3 separate reports, each containing source data, a table and a summary."""
    now = datetime.now().astimezone()
    summary_text = build_report(s, now)
    members_text = build_members_report(s, now)
    parking_text = build_parking_report(s, now)

    paths = [
        _write_report(s.report_path, summary_text),
        _write_report(s.report_members_path, members_text),
        _write_report(s.report_parking_path, parking_text),
    ]
    return paths


# --------------------------------------------------------------------------
# Input helpers (validation)
# --------------------------------------------------------------------------
YES_WORDS = {"y", "yes", "ใช่"}
NO_WORDS = {"n", "no", "ไม่", "ไม่ใช่"}


def warn(msg):
    print(f"  ! {msg}")


def ask(prompt):
    return input(prompt).strip()


def ask_int(prompt, lo=None, hi=None, blank_ok=False):
    while True:
        s = ask(prompt)
        if s == "" and blank_ok:
            return None
        try:
            v = int(s)
        except ValueError:
            warn(t("err_need_int"))
            continue
        if (lo is not None and v < lo) or (hi is not None and v > hi):
            warn(t("err_range", lo=lo, hi=hi) if hi is not None else t("err_min", lo=lo))
            continue
        return v


def ask_text(prompt, max_bytes, blank_ok=False, pattern=None, hint=""):
    while True:
        s = ask(prompt)
        if s == "":
            if blank_ok:
                return None
            warn(t("err_required"))
            continue
        if len(s.encode("utf-8")) > max_bytes:
            warn(t("err_too_long", max=max_bytes))
            continue
        if pattern and not re.fullmatch(pattern, s):
            warn(hint)
            continue
        return s


def ask_yes_no(prompt):
    while True:
        s = ask(f"{prompt} {t('yn_hint')}: ").lower()
        if s in YES_WORDS:
            return True
        if s in NO_WORDS:
            return False
        warn(t("err_yes_no"))


def choose(title, options):
    print(f"\n-- {title} --")
    for i, o in enumerate(options, 1):
        print(f"{i}) {o}")
    print(f"0) {t('back')}")
    return ask_int(t("select"), 0, len(options))


def choose_entity():
    c = choose(t("ttl_which"), [t("e_vehicles"), t("e_members"), t("e_parking")])
    return (None, "vehicle", "member", "parking")[c]


def pick_type(allow_blank=False):
    c = choose(t("ttl_vehicle_type"), [type_label(v) for v in VEHICLE_TYPES])
    if c == 0:
        if allow_blank:
            return None
        raise AppError("err_cancelled")
    return VEHICLE_TYPES[c - 1]


def pick_brand(blank_ok=False):
    """Choose a common brand by number; keep free-text fallback for Other."""
    options = VEHICLE_BRANDS
    print(f"\n-- {t('m_brand_select')} --")
    for i, brand in enumerate(options, 1):
        label = t("brand_other") if brand == "Other" else brand
        print(f"{i}) {label}")
    if blank_ok:
        print(f"0) {t('back')} / keep current")
    else:
        print(f"0) {t('back')}")
    while True:
        c = ask_int(t("select"), 0, len(options))
        if c == 0:
            if blank_ok:
                return None
            raise AppError("err_cancelled")
        brand = options[c - 1]
        if brand == "Other":
            return ask_text(t("p_brand_other"), 15, blank_ok=False)
        return brand


def ask_plate(blank_ok=False):
    return ask_text(t("p_plate"), 20, blank_ok, PLATE_RE, t("hint_plate"))


def ask_phone(blank_ok=False):
    return ask_text(t("p_phone"), 15, blank_ok, PHONE_RE, t("hint_phone"))


# --------------------------------------------------------------------------
# Menu actions
# --------------------------------------------------------------------------
def menu_add(s):
    c = choose(t("m_add"), [t("vehicle"), t("member")])
    if c == 1:
        plate = ask_plate()
        vtype = pick_type()
        brand = pick_brand()
        rec = s.add_vehicle(plate, vtype, brand)
        print("  " + t("ok_vehicle_added", id=rec["vehicle_id"]))
    elif c == 2:
        name = ask_text(t("p_name"), 30)
        phone = ask_phone()
        vid = ask_int(t("p_vehicle_id"), 1)
        rec = s.add_member(name, phone, vid)
        print("  " + t("ok_member_added", id=rec["member_id"]))


def menu_update(s):
    c = choose(t("m_update"), [t("vehicle"), t("member")])
    if c == 1:
        vid = ask_int(t("p_vehicle_id"), 1)
        cur = s.active_vehicle(vid)
        print("  " + t("cur_vehicle", plate=cur["plate"], type=type_label(cur["vehicle_type"]),
                       brand=cur["brand"]))
        plate = ask_plate(blank_ok=True)
        vtype = pick_type(allow_blank=True)
        brand = pick_brand(blank_ok=True)
        s.update_vehicle(vid, plate, vtype, brand)
        print("  " + t("ok_vehicle_updated"))
    elif c == 2:
        mid = ask_int(t("p_member_id"), 1)
        cur = s.active_member(mid)
        print("  " + t("cur_member", name=cur["name"], phone=cur["phone"], vid=cur["vehicle_id"]))
        name = ask_text(t("p_name"), 30, blank_ok=True)
        phone = ask_phone(blank_ok=True)
        vid = ask_int(t("p_vehicle_id"), 1, blank_ok=True)
        s.update_member(mid, name, phone, vid)
        print("  " + t("ok_member_updated"))


def menu_delete(s):
    c = choose(t("m_delete"), [t("vehicle"), t("member")])
    if c == 1:
        vid = ask_int(t("p_vehicle_id"), 1)
        v = s.active_vehicle(vid)
        if ask_yes_no(t("confirm_del_vehicle", id=vid, plate=v["plate"])):
            s.delete_vehicle(vid)
            print("  " + t("ok_vehicle_deleted"))
    elif c == 2:
        mid = ask_int(t("p_member_id"), 1)
        m = s.active_member(mid)
        if ask_yes_no(t("confirm_del_member", id=mid, name=m["name"])):
            s.delete_member(mid)
            print("  " + t("ok_member_deleted"))


def view_single(s):
    e = choose_entity()
    if not e:
        return
    rid = ask_int(t("p_id"), 1)
    if e == "vehicle":
        rec = s.view_vehicle(rid)
        print(text_table(veh_head(), vehicle_rows([rec], s.parked_map())))
    elif e == "member":
        rec = s.members.get(rid)
        if not rec:
            raise AppError("err_member_not_found", id=rid)
        print(text_table(mem_head(), member_rows([rec])))
    else:
        rec = s.parking.get(rid)
        if not rec:
            raise AppError("err_parking_not_found", id=rid)
        print(text_table(prk_head(), parking_rows([rec])))


def view_all(s):
    e = choose_entity()
    if e == "vehicle":
        print(text_table(veh_head(), vehicle_rows(s.vehicles.records(), s.parked_map())))
    elif e == "member":
        print(text_table(mem_head(), member_rows(s.members.records())))
    elif e == "parking":
        print(text_table(prk_head(), parking_rows(s.parking.records())))


def view_filter(s):
    e = choose_entity()
    if e == "vehicle":
        c = choose(t("ttl_filter_vehicles"), [t("f_type"), t("f_brand"), t("f_parked"),
                                              t("f_status")])
        if c == 0:
            return
        parked = s.parked_map()
        recs = s.vehicles.records()
        if c == 1:
            ty = pick_type()
            recs = [r for r in recs if r["vehicle_type"] == ty]
        elif c == 2:
            b = ask_text(t("p_brand"), 15).lower()
            recs = [r for r in recs if b in r["brand"].lower()]
        elif c == 3:
            want = ask_yes_no(t("q_show_parked"))
            recs = [r for r in recs if (r["status"] == 1 and r["vehicle_id"] in parked) == want]
        else:
            want = ask_yes_no(t("q_active_only"))
            recs = [r for r in recs if (r["status"] == 1) == want]
        print(text_table(veh_head(), vehicle_rows(recs, parked)))
    elif e == "member":
        want = ask_yes_no(t("q_active_members"))
        recs = [m for m in s.members.records() if (m["status"] == 1) == want]
        print(text_table(mem_head(), member_rows(recs)))
    elif e == "parking":
        c = choose(t("ttl_filter_parking"), [t("f_parked"), t("f_completed"), t("f_vehicle_id")])
        recs = s.parking.records()
        if c == 1:
            recs = [r for r in recs if r["status"] == 1]
        elif c == 2:
            recs = [r for r in recs if r["status"] == 0]
        elif c == 3:
            vid = ask_int(t("p_vehicle_id"), 1)
            recs = [r for r in recs if r["vehicle_id"] == vid]
        else:
            return
        print(text_table(prk_head(), parking_rows(recs)))


def view_stats(s):
    print()
    print(build_report(s, datetime.now().astimezone(), with_table=False, with_header=False))


def menu_view(s):
    actions = [view_single, view_all, view_filter, view_stats]
    while True:
        c = choose(t("m_view"), [t("v_single"), t("v_all"), t("v_filter"), t("v_stats")])
        if c == 0:
            return
        try:
            actions[c - 1](s)
        except AppError as e:
            warn(e)


def menu_entry(s):
    vid = ask_int(t("p_vehicle_id"), 1)
    free = s.free_slots()
    print("  " + t("free_slots_info", free=len(free), total=TOTAL_SLOTS))
    slot = ask_int(t("p_slot"), 1, TOTAL_SLOTS, blank_ok=True)
    rec = s.enter(vid, slot)
    print("  " + t("ok_parked", slot=rec["slot_no"], time=rec["time_in"]))


def menu_exit_vehicle(s):
    vid = ask_int(t("p_vehicle_id"), 1)
    rec = s.leave(vid)
    print("  " + t("ok_exit", slot=rec["slot_no"], time_in=rec["time_in"],
                   time_out=rec["time_out"]))
    print("  " + t("fee_line", fee=f"{rec['fee']:.2f}"))
    print("  " + t("fee_rate", rate=f"{RATE_PER_HOUR:.2f}", min=f"{MIN_FEE:.2f}"))


def menu_report(s):
    paths = generate_report(s)
    print("  " + t("ok_report", path=paths[0]))
    for path in paths[1:]:
        print("  " + path)


def get_current_member(s):
    if current_member_id is None:
        raise AppError("login_required")
    return s.active_member(current_member_id)


def user_vehicle(s):
    member = get_current_member(s)
    vid = member["vehicle_id"]
    if not vid:
        raise AppError("user_no_vehicle")
    return member, s.active_vehicle(vid)


def menu_user_view(s):
    member, vehicle = user_vehicle(s)
    parked = s.parked_map().get(vehicle["vehicle_id"])
    print(text_table(veh_head(), vehicle_rows([vehicle], s.parked_map())))
    print(text_table(mem_head(), member_rows([member])))
    if parked:
        print(text_table(prk_head(), parking_rows([parked])))
    else:
        history = [r for r in s.parking.records() if r["vehicle_id"] == vehicle["vehicle_id"]]
        if history:
            print(text_table(prk_head(), parking_rows(history[-10:])))


def menu_user_entry(s):
    _member, vehicle = user_vehicle(s)
    free = s.free_slots()
    if not free:
        raise AppError("err_lot_full")

    # User must choose a free parking slot instead of silently taking slot 1.
    print("  " + t("free_slots_info", free=len(free), total=TOTAL_SLOTS))
    print("  " + t("available_slots", slots=", ".join(map(str, free))))
    slot = ask_int(t("p_slot"), 1, TOTAL_SLOTS)
    rec = s.enter(vehicle["vehicle_id"], slot)
    print("  " + t("ok_parked", slot=rec["slot_no"], time=rec["time_in"]))


def menu_user_exit(s):
    _member, vehicle = user_vehicle(s)
    rec = s.leave(vehicle["vehicle_id"])
    print("  " + t("ok_exit", slot=rec["slot_no"], time_in=rec["time_in"],
                   time_out=rec["time_out"]))
    print("  " + t("fee_line", fee=f"{rec['fee']:.2f}"))
    print("  " + t("fee_rate", rate=f"{RATE_PER_HOUR:.2f}", min=f"{MIN_FEE:.2f}"))


def menu_user_history(s):
    _member, vehicle = user_vehicle(s)
    records = [r for r in s.parking.records() if r["vehicle_id"] == vehicle["vehicle_id"]]
    if not records:
        print("  " + t("none"))
        return
    print(text_table(prk_head(), parking_rows(records)))


MENU = [("1", "m_add", menu_add), ("2", "m_update", menu_update), ("3", "m_delete", menu_delete),
        ("4", "m_view", menu_view), ("5", "m_entry", menu_entry),
        ("6", "m_exit_vehicle", menu_exit_vehicle), ("7", "m_report", menu_report)]
LANG_KEY = "8"                    # "Change Language" entry in the main menu


def choose_language(allow_back=False):
    """Language screen. Returns "th" / "en", or None (exit at start-up / back when changing)."""
    while True:
        print(f"\n=== {bi('main_title')} ===")
        print(f"1) {TH['lang_th_name']}")
        print(f"2) {EN['lang_en_name']}")
        print(f"3) {bi('back') if allow_back else bi('exit_program')}")
        choice = ask(f"{bi('select_language')}: ")
        if choice == "1":
            return "th"
        if choice == "2":
            return "en"
        if choice == "3":
            return None
        warn(bi("invalid_lang_choice"))


def register_member(s):
    """Register a new member and one vehicle using the existing data schema."""
    print(f"\n=== {t('register_title')} ===")
    name = ask_text(t("p_name"), 30)
    phone = ask_phone()
    plate = ask_plate()
    vtype = pick_type()
    brand = pick_brand()

    # Create the vehicle first because the existing member record stores vehicle_id.
    vehicle = s.add_vehicle(plate, vtype, brand)
    try:
        member = s.add_member(name, phone, vehicle["vehicle_id"])
    except Exception:
        # Avoid leaving an orphan vehicle if member creation unexpectedly fails.
        try:
            s.delete_vehicle(vehicle["vehicle_id"])
        except Exception:
            pass
        raise

    print("  " + t("register_success", id=member["member_id"]))


def login(s):
    global current_role, current_member_id
    while True:
        c = choose(t("role_title"), [t("role_admin"), t("role_user"), t("role_register")])
        if c == 0:
            return False
        if c == 1:
            code = ask(t("p_admin_code"))
            if code == ADMIN_CODE:
                current_role, current_member_id = "admin", None
                return True
            warn(t("login_failed"))
        elif c == 2:
            mid = ask_int(t("p_login_member"), 1)
            try:
                s.active_member(mid)
                current_role, current_member_id = "user", mid
                return True
            except AppError:
                warn(t("login_failed"))
        elif c == 3:
            try:
                register_member(s)
            except AppError as e:
                warn(e)


def main_loop(s):
    """Run the role-specific main menu. Returns True when the user asks to change language."""
    if current_role == "user":
        actions = {
            "1": menu_user_view,
            "2": menu_user_entry,
            "3": menu_user_exit,
            "4": menu_user_history,
        }
        while True:
            print(f"\n=== {t('user_title')} ===")
            print(f"1) {t('m_view')} ({t('user_vehicle_only')})")
            print(f"2) {t('m_entry')}")
            print(f"3) {t('m_exit_vehicle')}")
            print(f"4) {t('e_parking')}")
            print(f"5) {t('m_language')}")
            print(f"0) {t('m_exit')}")
            choice = ask(t("select"))
            if choice == "0":
                return False
            if choice == "5":
                return True
            fn = actions.get(choice)
            if not fn:
                warn(t("invalid_main"))
                continue
            try:
                fn(s)
            except AppError as e:
                warn(e)
    else:
        actions = {k: fn for k, _, fn in MENU}
        while True:
            print(f"\n=== {t('main_title')} [{t('role_admin')}] ===")
            for k, key, _ in MENU:
                print(f"{k}) {t(key)}")
            print(f"{LANG_KEY}) {t('m_language')}")
            print(f"0) {t('m_exit')}")
            choice = ask(t("select"))
            if choice == "0":
                return False
            if choice == LANG_KEY:
                return True
            fn = actions.get(choice)
            if not fn:
                warn(t("invalid_main"))
                continue
            try:
                fn(s)
            except AppError as e:
                warn(e)


def run_interactive(s):
    while login(s):
        while main_loop(s):
            code = choose_language(allow_back=True)
            if code:
                set_language(code)
            else:
                break
        # Logout after leaving a role menu; next loop requires login again.
        global current_role, current_member_id
        current_role, current_member_id = None, None
        if current_role is None:
            # Keep the existing simple flow: exit after a completed session.
            break
    print(t("goodbye"))


# --------------------------------------------------------------------------
# Demo data  (data values themselves are not translated)
# --------------------------------------------------------------------------
def seed(s, n):
    if s.vehicles.count:
        print(t("seed_skipped"))
        return
    rng = random.Random(42)
    brands = ["Toyota", "Honda", "Nissan", "Mazda", "Mitsubishi", "Isuzu", "Suzuki"]
    names = ["สมชาย", "วิภา", "มานี", "Anan", "Malee", "Preecha", "Nattaya", "John Smith"]
    letters = "ABCDEFGHJKLMNPQRSTUVWXYZ"
    clock = datetime.now() - timedelta(days=10)
    vids, used = [], set()
    for _ in range(n):
        clock += timedelta(minutes=rng.randint(1, 30))
        plate = ""
        while not plate or plate in used:
            plate = f"{rng.choice(letters)}{rng.choice(letters)}-{rng.randint(1000, 9999)}"
        used.add(plate)
        vtype = "Car" if rng.random() < 0.7 else "Motorcycle"
        vids.append(s.add_vehicle(plate, vtype, rng.choice(brands), now=clock)["vehicle_id"])
    for vid in rng.sample(vids, max(1, n // 5)):
        s.add_member(rng.choice(names), "08" + "".join(rng.choice("0123456789") for _ in range(8)),
                     vid, now=clock)
    parked = []
    for _ in range(n * 3):
        clock += timedelta(minutes=rng.randint(10, 90))
        if parked and (rng.random() < 0.55 or len(parked) >= 10):
            s.leave(parked.pop(rng.randrange(len(parked))), now=clock)
        else:
            vid = rng.choice([v for v in vids if v not in parked])
            s.enter(vid, slot=rng.choice(s.free_slots()), now=clock)
            parked.append(vid)
    for vid in rng.sample([v for v in vids if v not in parked], min(3, n // 10)):
        s.delete_vehicle(vid)
    print(t("seed_done", n=n, members=s.members.count, parking=s.parking.count))


# --------------------------------------------------------------------------
# Command line
# --------------------------------------------------------------------------
class LocalizedHelpFormatter(argparse.HelpFormatter):
    def add_usage(self, usage, actions, groups, prefix=None):
        if prefix is None:
            prefix = t("help_usage") + ": "
        super().add_usage(usage, actions, groups, prefix)


class LocalizedParser(argparse.ArgumentParser):
    def error(self, message):
        self.print_usage(sys.stderr)
        self.exit(2, t("arg_error", msg=message) + "\n")


def build_parser():
    ap = LocalizedParser(description=t("help_desc"), add_help=False,
                         formatter_class=LocalizedHelpFormatter)
    g = ap.add_argument_group(t("help_options"))
    g.add_argument("-h", "--help", action="help", help=t("help_help"))
    g.add_argument("--data-dir", default="data", help=t("help_data_dir"))
    g.add_argument("--seed", type=int, metavar="N", help=t("help_seed"))
    g.add_argument("--report", action="store_true", help=t("help_report"))
    g.add_argument("--lang", type=str.lower, choices=sorted(TRANSLATIONS),
                   metavar="{th,en}", help=t("help_lang"))
    return ap


def main(argv=None):
    for stream in (sys.stdout, sys.stdin, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8")
        except Exception:
            pass

    # Pre-scan --lang so that --help and argparse messages use the chosen language.
    pre = argparse.ArgumentParser(add_help=False, allow_abbrev=False)
    pre.add_argument("--lang", type=str.lower, choices=sorted(TRANSLATIONS))
    known, _ = pre.parse_known_args(argv)
    set_language(known.lang or "th")

    args = build_parser().parse_args(argv)
    interactive = not (args.seed or args.report)

    s = None
    try:
        if args.lang:
            set_language(args.lang)
        elif interactive:
            code = choose_language()
            if code is None:
                return 0
            set_language(code)

        try:
            s = ParkingSystem(args.data_dir)
        except CorruptFileError as e:
            print(t("corrupt_notice", error=e))
            return 2

        if args.seed:
            seed(s, args.seed)
        if interactive:
            run_interactive(s)
    except (KeyboardInterrupt, EOFError):
        print()
    finally:
        if s is not None:
            try:
                print(t("report_written", path=generate_report(s)))
            finally:
                s.close()
    return 0


if __name__ == "__main__":
    sys.exit(main())